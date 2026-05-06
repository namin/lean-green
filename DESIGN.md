# lean-black — design

A verified Black-faithful reflective interpreter in Lean 4, with
LLM-driven proposer/gate cascade and full conservative-extension
soundness for governed reflective modifications.

This document is the plan. The artifact is built incrementally
following it; the document gets refined as the build clarifies the
design.

## What lean-black is

A Lean 4 implementation of the core of Black's reflective
architecture (Asai, Matsuoka, Yonezawa 1996). Three load-bearing
properties:

1. **Causal connection.** A `set!` against the meta-env's
   `base-apply` from inside `(em ...)` observably changes how the
   base level evaluates applications. This is Smith's "the meta-level
   is data" actually realized — not modeled by a table of indexed
   modifications, but by a heap cell whose mutation propagates to
   future dispatch.

2. **Parametric verified governance.** Modifications to meta-env
   bindings are gated by a current `BlackPolicy`, drawn from a
   verified policy table. Soundness is parameterized over an
   architectural floor `P : Val → Val → Prop`; the canonical
   instance is conservative extension. Each policy in the table has
   a soundness theorem against `P` proved in Lean. Switching
   policies is itself a reflective step (`installPolicy`).

3. **LLM-driven proposer.** A Bedrock-mediated cascade where Claude
   proposes Black-source modifications, which are elaborated and
   admitted (or refused) under the active policy. The kernel
   discipline is real: the LLM cannot bypass the gate, and the gate
   cannot generate proposals. This is the proposer/gate architecture
   from the keynote thesis, instantiated with verified governance.

## What's verified

Three layers, each with its own headline theorem:

**Structural.** `numGuardPolicy` admits exactly closures of a
recognized syntactic shape; `multnExactPolicy` admits exactly
closures of the strict multn pattern with delegating else-branch.
These are inversions of the policy's pattern-matching definition,
proved by case analysis.

**Operational.** Every policy in the verified table is sound for
the architectural floor `P` (= `ConservativeExt`). For
`multnExactPolicy`, this is the headline result:

```
theorem multnExact_soundForCE_first_install :
    multnExactPolicy .builtinBaseApply new = true →
    OrigBoundIn s.heap .builtinBaseApply new →
    NumQBoundIn s.heap (cenvOf new) →
    HeapValid s.heap →
    EnvValid metaEnv s.heap →
    callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s.heap s''.heap
```

Here `ValVis` is the value-equivalence relation defined below
(values structurally equal up to closure-environment refinement).
The four install-protocol hypotheses encode what the runner
guarantees when it admits a modification via
`(em (let orig base-apply (set! base-apply <PROP>)))` from a clean
state:

- **`OrigBoundIn`** — closure cenv binds `"orig"` to a heap cell
  holding `.builtinBaseApply` (the captured original)
- **`NumQBoundIn`** — cenv binds `"num?"` to `.prim "num?"`, so the
  body's cond evaluation can resolve
- **`HeapValid`** — every heap cell holds a `ValValid` value
- **`EnvValid metaEnv`** — meta-env's bindings point to valid heap
  cells

The first two are install-time facts; the latter two are runtime
invariants the runner maintains across any sequence of admitted
modifications. Each is a 1-3 line predicate.

**Infrastructure.** The framing theorem that makes the operational
proof possible:

```
theorem applyDirect_frame :
  WFCtx metaEnv metaEnv metaEnv s_a s_b →
  ValVis op_a op_b s_a.heap s_b.heap →
  ListValVis args_a args_b s_a.heap s_b.heap →
  EnvVis metaEnv metaEnv s_a.heap s_b.heap →
  applyDirect fuel ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
  ∃ r_b s_b',
    applyDirect fuel ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
    ValVis r_a r_b s_a'.heap s_b'.heap ∧
    WFCtx metaEnv metaEnv metaEnv s_a' s_b' ∧
    HeapExt s_a s_a' ∧ HeapExt s_b s_b' ∧
    EnvVis metaEnv metaEnv s_a'.heap s_b'.heap
```

Plus parallel statements for `eval`, `evalList`, `applyVia`. Proved
mutually by induction on fuel.

`WFCtx`, `HeapExt`, and `ListValVis` are bundling abstractions that
emerged during the build — see the *Refinements* section below.

## Why ValVis

The natural same-`Val` framing (*"if eval succeeds in state s, it
succeeds with the same `Val` in state s ++ extras"*) is **provably
false** when the language has closures with captured envs. The `lam`
case is the counterexample: `eval (.lam ps body) env_a metaEnv s_a
= some (.closure ps body env_a, s_a)`. With `env_a ≠ env_b`, the
two closures returned have different captured envs — they're
distinct `Val`s.

This is a known issue in PL semantics. The standard fix
(CakeML, Kumar 2016 Ch. 3) is **syntax-based data refinement**:
two closures relate iff their bodies are equal *and* their captured
envs are pointwise related. Two values relate iff structurally
equal up to closure refinement. Two envs relate iff they look up
to related values.

CakeML uses this for compiler verification (closures relate across
compilation phases). For lean-black, source and target are the same
language, so the relation simplifies — closure bodies are *equal*,
not "compiles to". The infrastructure is otherwise the same.

```lean
mutual
def ValVis : Val → Val → Heap → Heap → Prop
  | .num n_a,  .num n_b,  _,   _   => n_a = n_b
  | .bool b_a, .bool b_b, _,   _   => b_a = b_b
  | .nilV,     .nilV,     _,   _   => True
  | .sym s_a,  .sym s_b,  _,   _   => s_a = s_b
  | .prim n_a, .prim n_b, _,   _   => n_a = n_b
  | .builtinBaseApply, .builtinBaseApply, _, _ => True
  | .cons x_a y_a, .cons x_b y_b, h_a, h_b =>
      ValVis x_a x_b h_a h_b ∧ ValVis y_a y_b h_a h_b
  | .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ body_a = body_b ∧ EnvVis cenv_a cenv_b h_a h_b
  | _, _, _, _ => False

def EnvVis : Env → Env → Heap → Heap → Prop :=
  fun env_a env_b h_a h_b =>
    ∀ x, match env_a.lookup x, env_b.lookup x with
      | none, none => True
      | some i_a, some i_b =>
          match h_a[i_a]?, h_b[i_b]? with
          | some v_a, some v_b => ValVis v_a v_b h_a h_b
          | _, _ => False
      | _, _ => False
end
```

The mutual recursion is not structural — `ValVis` on closures
recurses into `EnvVis`, which iterates over names looking up `Val`s
and recurses back. **In practice we use depth-indexed approximations
`ValVis_aux n` and `EnvVis_aux n` (see Refinements below), with
`ValVis = ∀ n, ValVis_aux n`.** This gives `ValVis_aux` structural
recursion in `Nat` and avoids the well-founded-measure dance — it's
also how CakeML's analogous `_n`-indexed relations are organized.

State relations come in two flavors:

```lean
-- Cross-side: between s_a and s_b. Same policy + heap relation.
def StateExt (s_a s_b : RunState) : Prop :=
  s_a.policy = s_b.policy ∧ ∃ extras, s_b.heap = s_a.heap ++ extras

-- Same-side: between s and the eval-result state. Heap-prefix only;
-- the policy may change (via installPolicy), so no policy constraint.
def HeapExt (s_a s_b : RunState) : Prop :=
  ∃ extras, s_b.heap = s_a.heap ++ extras
```

Both are needed; see Refinements.

## Substrate (the interpreter)

A four-way mutual block (`eval` / `evalList` / `applyVia` /
`applyDirect`) over fuel-based functional big-step semantics. This
is the standard CakeML pattern (their "clock", their Kumar 2016
§3.4 divergence-preservation argument). Fuel monotonicity is a
prerequisite lemma proved by induction; we reuse it.

Key types:

```lean
mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | nilV    : Val
  | cons    : Val → Val → Val
  | sym     : String → Val
  | closure : List String → Expr → Env → Val
  | prim    : String → Val
  | builtinBaseApply : Val

inductive Expr where
  | num | bool | quote | var | ifte | lam | app | set | em
  | primApp | letE | seq | installPolicy

inductive Env where
  | nil  : Env
  | cons : String → Nat → Env → Env  -- name → heap-index
end

abbrev Heap := List Val

abbrev BlackPolicy := Val → Val → Bool

structure RunState where
  heap   : Heap
  policy : BlackPolicy
```

Reflective constructs:

- `(em body)` — body evaluates with metaEnv as the env-in-scope, so
  `base-apply` is a name `set!`-able from inside.
- `(set! x e)` — if the target is a meta-env binding (same heap-cell
  index in both `env` and `metaEnv`), the current policy gates the
  mutation. Plain mutations are not gated.
- `(install-policy n)` — replaces the current policy with the n-th
  entry of the verified policy table.
- `(prim-apply f args)` — direct application bypassing the meta-env
  base-apply lookup. Replacement closures use this to call captured
  originals without infinite regress (analog of Black's
  `primitive-EM`).

## Layout

```
lean-black/
├── lakefile.lean
├── lean-toolchain
├── LeanBlack.lean           — top-level imports
├── LeanBlack/
│   ├── Black.lean           — Val, Expr, Env, Heap, RunState, eval, ...
│   ├── Bisim.lean           — ValVis, EnvVis, StateExt, framing theorems
│   ├── Policies.lean        — BlackPolicy, library, verifiedTable
│   ├── Soundness.lean       — multnExact_soundForCE_first_install
│   ├── Bedrock.lean         — `aws bedrock-runtime invoke-model` wrapper
│   ├── Elab.lean            — proposal elaboration via `lake env lean --run`
│   └── Runner.lean          — one-round cascade
├── Smoke.lean               — `lake exe smoke`: un-governed and governed demos
├── BedrockSmoke.lean        — `lake exe bedrock-smoke`: connectivity check
├── RunnerMain.lean          — `lake exe runner [N]`: N rounds of LLM cascade
└── DESIGN.md                — this file
```

## Verification structure

The proof chain has three levels:

```
                multnExact_soundForCE_first_install
                            ↑
                  ┌─────────┴──────────┐
                  ↓                    ↓
        multnExact_CE_num_case   multnExact_CE_nonnum_case
        (vacuous, no Val rel)    (uses ValVis)
                  ↑                    ↑
                  ↓                    ↓
       applyDirect_num_returns_none    applyDirect_frame
                                           ↑
                                  fuel_mono + ValVis machinery
```

The numerical case is vacuous: `applyDirect` returns `none` on
`.num` operators (the `_ => none` fallthrough), so the CE premise
on numerical operators is unsatisfiable.

The non-numerical case requires unfolding the closure body's
evaluation:
- alloc `op` and `listToVal operands` as params; eval body
- body is `.ifte (num? op) t (orig op args)`
- cond evaluates to `.bool false` (using `OpNotNum` and the cenv's
  `num?` binding from `NumQBoundIn`)
- else-branch evaluates `(orig op args)`: lookup `orig` →
  `.builtinBaseApply` (from `OrigBoundIn`); lookup `op`/`args` →
  the freshly-allocated values
- `applyDirect .builtinBaseApply [op, listToVal operands]`:
  builtin dispatch → `applyDirect op operands` directly
- The outer `h_old` says `applyDirect fuel ptable op operands metaEnv s
  = some (r, s')`. The inner call here uses extended state. The
  framing theorem `applyDirect_frame` bridges them:
  `ValVis op op` (reflexivity), `args_a = args_b = operands`, the
  state difference is the param allocations. The framing gives
  `applyDirect on inner state` succeeds with some `r'` and
  `ValVis r r'`.

`fuel_mono` provides the fuel buffer for the closure-body overhead.

## What this isn't

- **Not a Black-to-CakeML compiler.** CakeML's
  `compiler/scheme/` is a useful reference (their Scheme source
  semantics is structurally close to ours: value type with closures
  and pairs, store with `Mut`/`Pair` entries, `fresh_loc`
  allocation), but lean-black is a self-contained Lean 4
  development that doesn't emit anything externally.

- **Not a port of full CakeML semantics.** No exception handling,
  modules, type system, etc. Just the value-bisimulation
  infrastructure for first-class closures with state, on a
  Black-shaped interpreter.

- **Not aimed at full meta-circular faithfulness.** Stage 1
  simplifications: only `base-apply` is reified in the meta-env
  (not `base-eval`, `eval-if`, etc.); fuel rather than meta-
  continuations; one meta-env (not a per-level tower); `(em (em
  body))` is currently the same as `(em body)`.  These are stage 2
  extensions; the architecture supports them.

## Estimated scope

Rough budget for the build, with Kumar 2016 as reference. **These
are revised estimates** — initial ones in earlier drafts were ~50%
too low, mostly because the bisimulation infrastructure required
several supporting abstractions (`WFCtx`, `HeapExt`, `ListValVis`,
`ValValid` invariant) that weren't in the first sketch:

- Substrate (`Black.lean`): ~280 LOC (interpreter, primitives,
  initState, evalProgram). Standard.
- `Bisim.lean`: ~1500-2000 LOC. Includes the depth-indexed
  `ValVis_aux` / `EnvVis_aux` mutual definition, the universal-depth
  versions, `StateExt` and `HeapExt` (both needed — see
  *Refinements* below), validity machinery (`ValValid`, `HeapValid`,
  `EnvValid`), `WFCtx` invariant bundle, two-sided heap-extension
  lemmas (`ValVis_aux_extends`, `EnvVis_aux_extends` mutually
  proved), `ListValVis`, characterization lemmas
  (`ValVis_bool_false_iff`), and the `frame` mutual theorem itself.
  Roughly half the LOC is the framing proof; the other half is
  supporting abstractions and lemmas.
- `Policies.lean`: ~270 LOC (BlackPolicy, library, structural
  soundness theorems via `split at h`, install-protocol predicates,
  conditional CE soundness for multn).
- LLM cascade glue (`Bedrock.lean` / `Elab.lean` / `Runner.lean` /
  `RunnerMain.lean`): ~600 LOC. Standard Bedrock wrapper +
  spliced-Lean-source elaboration + one-round orchestrator. (Ports
  cleanly from the lean-grey precursor.)

Total: ~2700-3200 LOC. Roughly 8-12 focused sessions to assemble,
build, and prove. The framing theorem alone is the bulk: each of
the four mutual functions has many cases, each requiring 30-150 LOC
following established proof templates.

## Demo

```bash
lake exe smoke               # un-governed and governed scenes
lake exe bedrock-smoke       # connectivity check
lake exe runner [N]          # N rounds of LLM cascade
```

The smoke test demonstrates the architectural claim concretely:

- *Un-governed* (default `acceptAllPolicy`): the multn pattern works
  via `set! base-apply` from inside `em`, and so does a malicious
  modification that overwrites `base-apply` with a constant —
  breaking `(+ 1 2)`. Reflection without governance.
- *Governed* (`installPolicy idx_numGuard`): the same malicious
  modification is refused (returns `false`); `(+ 1 2)` still
  returns `3`; the multn pattern is admitted.

The runner exercises the full cascade against Bedrock: Claude
proposes a multn-shaped wrapper as Lean source for an `Expr`, the
elaborator wraps and runs it under the active policy, the verdict
is admitted/refused/elab-error.

## Refinements (lessons from the build)

These are abstractions and details that emerged during construction
and weren't in the initial sketch. They're load-bearing for the
proofs to go through, so future readers should know about them
upfront.

### Depth-indexed bisimulation is the primary approach

Earlier drafts of this document framed depth-indexing as a fallback
("if the well-founded measure doesn't work, use fuel-indexed
family"). It turned out to be the right primary choice: well-founded
recursion through arbitrary heap-looked-up `Val`s doesn't have a
natural measure, while depth-indexing gives `ValVis_aux` structural
recursion in `Nat`. The "real" relations are
`ValVis = ∀ n, ValVis_aux n` and `EnvVis = ∀ n, EnvVis_aux n`.

This matches CakeML's pattern (their relations are likewise indexed
by an approximation depth).

### `HeapExt` vs `StateExt`

`StateExt s_a s_b` (cross-side, with same-policy constraint) is the
right hypothesis between sides — set!-policy interactions need both
sides to use the same policy. But `installPolicy` *changes* the
policy, so same-side state evolution s_a → s_a' breaks `StateExt`.
We need a separate `HeapExt s_a s_a' := ∃ extras, s_a'.heap = s_a.heap ++ extras`
(heap-only extension, no policy constraint) for the framing's
same-side conclusions. Both relations live in `Bisim.lean`.

### `WFCtx` invariant bundle

The framing theorem requires a bundle of invariants:
`StateExt s_a s_b` + `HeapValid s_a.heap`, `HeapValid s_b.heap` +
`EnvValid env_a s_a.heap`, `EnvValid env_b s_b.heap` +
`EnvValid metaEnv s_a.heap`, `EnvValid metaEnv s_b.heap`. Together
these are the preconditions `EnvVis_aux_extends` needs. Bundling
them in a `WFCtx` structure is essential — passing seven separate
hypotheses through every inner case is unworkable.

```lean
structure WFCtx (env_a env_b metaEnv : Env) (s_a s_b : RunState) : Prop where
  state_ext : StateExt s_a s_b
  hv_a, hv_b   : HeapValid s_{a,b}.heap
  ev_a, ev_b   : EnvValid env_{a,b} s_{a,b}.heap
  em_a, em_b   : EnvValid metaEnv s_{a,b}.heap
```

The framing theorem takes `WFCtx` as input and produces `WFCtx` for
the result state.

### `ValValid` outputs in framing

To chain framing across multi-step recursive cases (notably `.app`'s
3-step trace: eval f → evalList args → applyVia), the framing
conclusion needs to produce `ValValid r_a s_a'.heap` and
`ValValid r_b s_b'.heap` so the result values can be lifted via
`ValVis_extends` into subsequently-extended heaps. This wasn't
anticipated in the initial sketch; framing's conclusion needs
strengthening to produce these.

### Pointwise `ListValVis`

For `applyVia` / `applyDirect` framing, the args lists `args_a` and
`args_b` need pointwise `ValVis`, not just length equality.
Captured by:

```lean
def ListValVis : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVis x y h_a h_b ∧ ListValVis xs ys h_a h_b
  | _,       _,       _,   _   => False
```

`evalList`'s framing conclusion produces `ListValVis rs_a rs_b`;
`applyVia` / `applyDirect` framing takes it as a hypothesis.

### `.quote` and `ClosedVal`

The `.quote v` case requires `ValVis v v` across two different
heaps. For atomic Vals (numbers, booleans, etc.), this is trivial;
for `.cons` and `.closure`, it requires validity hypotheses. The
honest fix is a `ClosedVal v` predicate restricting quoted Vals to
those without closure references, or assuming `ValValid v` on both
heaps. Stage 3 work item.

## Risks

- **Sub-cases in framing are tedious.** Each function in the mutual
  block has many cases (`eval` has 13). The pattern is uniform but
  verbose, similar to fuel monotonicity. The proof template
  (`rw [F.eq_def]; simp only at h ⊢; cases hr : F n ... | none =>
  ... | some pr => ...; ih_F ...`) is established and works; the
  remaining work is mostly typing.

- **Closure's body-equality requirement might be too strong.** The
  framing requires `body_a = body_b` for closures to relate. If the
  closures we hand to `applyDirect` are produced by *different*
  evaluations, their bodies are equal (we're not compiling), so this
  should hold automatically.

These are sequencing risks, not blocking risks — none require new
conceptual work beyond what the design lays out.

## References

- `docs/Kumar_2016_thesis.pdf` — primary inspiration. Chapter 2
  (shallow→deep translation, refinement invariants), Chapter 3
  (verified compiler, data refinement for closures, fuel-based
  divergence preservation).
- `docs/CakeML_Kumar_2014.pdf` — the foundational POPL paper.
- `cakeml/compiler/scheme/` — verified Scheme-to-CakeML compiler
  in HOL4. Source semantics (`scheme_semanticsScript.sml`) is
  structurally close to lean-black's (value type with closures and
  pairs, store with `Mut`/`Pair` entries, `fresh_loc` allocation).
  Useful as a concrete reference for value/env/store handling.
- `black/black.scm` — Asai et al.'s reference implementation of
  Black. lean-black is a Lean 4 reimplementation of the core
  reflective architecture.

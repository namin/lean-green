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
    callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s.heap s''.heap
```

Here `ValVis` is the value-equivalence relation defined below
(values structurally equal up to closure-environment refinement).
The `OrigBoundIn` and `NumQBoundIn` hypotheses encode the install
protocol — what the runner guarantees when it admits a modification
via `(em (let orig base-apply (set! base-apply <PROP>)))` from a
state where `base-apply` is `builtinBaseApply` and `cenv` extends
the standard initial bindings.

**Infrastructure.** The framing theorem that makes the operational
proof possible:

```
theorem applyDirect_frame :
  StateExt s_a s_b →
  EnvVis env_a env_b s_a.heap s_b.heap →
  ValVis op_a op_b s_a.heap s_b.heap →
  args_a.length = args_b.length →
  (∀ i (h_lt : i < args_a.length),
    ValVis (args_a.get ⟨i, h_lt⟩) (args_b.get ⟨i, by ...⟩)
      s_a.heap s_b.heap) →
  EnvVis metaEnv metaEnv s_a.heap s_b.heap →
  applyDirect fuel ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
  ∃ r_b s_b',
    applyDirect fuel ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
    ValVis r_a r_b s_a'.heap s_b'.heap ∧
    StateExt s_a' s_b'
```

Plus parallel statements for `eval`, `evalList`, `applyVia`. Proved
mutually by induction on fuel.

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
and recurses back. The well-founded measure is the size of the
`Val` (treating closure size as the syntactic size of the body
plus the env's binding count). Standard CakeML technique.

State extension is straightforward:

```lean
def StateExt (s_a s_b : RunState) : Prop :=
  s_a.policy = s_b.policy ∧ ∃ extras, s_b.heap = s_a.heap ++ extras
```

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

Rough budget for the build, with Kumar 2016 as reference:

- Substrate (`Black.lean`): ~280 LOC (interpreter, primitives,
  initState, evalProgram). Standard.
- `Bisim.lean`: ~130 LOC (definitions, well-founded measure,
  reflexivity/transitivity helpers, `EnvValid.envVis_self`).
- `Policies.lean`: ~180 LOC (BlackPolicy, library, structural
  soundness theorems via `split at h`).
- Fuel monotonicity (mutual block): ~250 LOC. Established
  technique: `rw [F.eq_def]; simp only at h ⊢; cases hr : F n ...
  | none => ... | some pr => rw [hr] at h; simp only at h; have hr'
  := ih_F ...; rw [hr']; simp only; ...`. The eval block has 13
  cases; each follows the template.
- Framing (`applyDirect_frame` + companions, mutual): ~400 LOC.
  Same template, threading `ValVis`/`EnvVis` invariants. The
  closure case in `applyDirect` is where `EnvVis` extension matters:
  param indices differ between `s_a` and `s_b`, but the values
  allocated are `ValVis`-related (input args were related), so the
  extended envs remain `EnvVis`-related, and the body's eval
  preserves the relation by IH.
- `multnExact_soundForCE_first_install` (closure-body trace using
  `applyDirect_frame` at the inner step): ~150 LOC.
- LLM cascade glue (`Bedrock.lean` / `Elab.lean` / `Runner.lean` /
  `RunnerMain.lean`): ~600 LOC. Standard Bedrock wrapper plus a
  spliced-Lean-source elaboration step plus a one-round orchestrator.

Total: ~2000 LOC across all files. Roughly 4-6 focused sessions
to assemble, build, and prove.

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

## Risks

- **Mutual `ValVis`/`EnvVis` definition might not elaborate
  cleanly.** Lean 4 supports well-founded mutual recursion but the
  termination measure has to satisfy the kernel. If the natural
  size measure doesn't work, fall back to a fuel-indexed family
  `ValVis_n`/`EnvVis_n` and prove framing for sufficient depth.
  Less elegant but always works.

- **Sub-cases in framing might be tedious.** Each function in the
  mutual block has many cases (`eval` has 13). The pattern is
  uniform but verbose, similar to fuel monotonicity. No conceptual
  novelty per case, just typing.

- **Closure's body-equality requirement might be too strong.** The
  framing requires `body_a = body_b` for closures to relate. If the
  closures we hand to `applyDirect` are produced by *different*
  evaluations, their bodies are equal (we're not compiling), so this
  should hold automatically. But proving it for specific use cases
  may need lemmas about how eval preserves body identity.

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

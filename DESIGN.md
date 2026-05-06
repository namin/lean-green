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
theorem multnExact_soundForCE_first_install
    (h_admit : multnExactPolicy .builtinBaseApply new = true)
    (h_fuel  : fuel ≥ 2)
    (h_old   : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
                 = some (r, s'))
    (install : InstallFacts new s.heap)
    (wf      : RuntimeWF new metaEnv op operands s.heap)
    (sf      : SetFreeWF op operands s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap
```

The eleven invariants are bundled into three structures, grouped
by load-bearing role:

```
structure InstallFacts (new : Val) (heap : Heap) : Prop where
  orig : OrigBoundIn heap .builtinBaseApply new
  numq : ∃ ps body cenv, new = .closure ps body cenv ∧ NumQBoundIn heap cenv

structure RuntimeWF (new metaEnv op operands heap : ...) : Prop where
  hv_heap      : HeapValid heap
  ev_meta      : EnvValid metaEnv heap
  ev_cenv      : ∀ ps body cenv', new = .closure ps body cenv' → EnvValid cenv' heap
  vv_op        : ValValid op heap
  lvv_operands : ListValValid operands heap

structure SetFreeWF (op operands heap : ...) : Prop where
  sf_heap      : HeapSetFree heap
  sf_op        : SetFreeVal op
  sf_operands  : SetFreeListVal operands
```

Here `ValVis` is the value-equivalence relation defined below
(values structurally equal up to closure-environment refinement).

- **`InstallFacts`** captures what the runner guarantees when it
  admits a modification via
  `(em (let orig base-apply (set! base-apply <PROP>)))` from a
  clean state: `OrigBoundIn` (closure cenv binds `"orig"` to a
  heap cell holding `.builtinBaseApply`) and `NumQBoundIn` (cenv
  binds `"num?"` to `.prim "num?"`, so the body's cond evaluation
  can resolve).
- **`RuntimeWF`** captures the runtime well-formedness invariants
  the runner inductively maintains: `HeapValid`, `EnvValid
  metaEnv`, `EnvValid (cenvOf new)` for the captured cenv,
  `ValValid op`, and `ListValValid operands`.
- **`SetFreeWF`** captures the Path-A side-conditions: the heap
  and the `(op, operands)` triple lie in `frame`'s set-free
  domain. The runner trivially maintains these — it only
  constructs values from `.lam` bodies and atomic literals, never
  from `.set`-bearing source. See *Refinements / `.set` and Path A*
  below for why this restriction is the principled answer rather
  than a missing proof.
- **`fuel ≥ 2`** — the closure-body trace evaluates an `evalList`
  over a 2-element argument list, which decrements fuel twice
  internally; `fuel ≥ 2` ensures all those internal calls have
  enough fuel to succeed. Trivially satisfied in practice
  (`Smoke.lean` runs at `fuel = 10000`).

The `InstallFacts` are install-time facts (set up once at the
moment of admission). The `RuntimeWF` invariants are inductive on
the runtime: heap and env validity propagate naturally, and the
`op`/`operands` validity follows from the fact that base-level
evaluations on a `HeapValid` heap produce `ValValid` values. The
`SetFreeWF` side-conditions are similarly inductive on the
runner's value-construction protocol. The fuel bound is a
precondition the runner must establish at the call site.

**Infrastructure.** The framing theorem that makes the operational
proof possible:

```
theorem applyDirect_frame :
  WFCtx metaEnv metaEnv metaEnv s_a s_b →
  ValVis op_a op_b s_a.heap s_b.heap →
  ListValVis args_a args_b s_a.heap s_b.heap →
  EnvVis metaEnv metaEnv s_a.heap s_b.heap →
  ValValid op_a s_a.heap → ValValid op_b s_b.heap →
  ListValValid args_a s_a.heap → ListValValid args_b s_b.heap →
  applyDirect fuel ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
  ∃ r_b s_b',
    applyDirect fuel ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
    ValVis r_a r_b s_a'.heap s_b'.heap ∧
    WFCtx metaEnv metaEnv metaEnv s_a' s_b' ∧
    HeapExt s_a s_a' ∧ HeapExt s_b s_b' ∧
    EnvVis metaEnv metaEnv s_a'.heap s_b'.heap ∧
    ValValid r_a s_a'.heap ∧ ValValid r_b s_b'.heap
```

Plus parallel statements for `eval`, `evalList`, `applyVia`. Proved
mutually by induction on fuel. The `eval`/`evalList` branches don't
require `ValValid` on inputs — they produce `ValValid`/`ListValValid`
outputs from heap and env validity carried in `WFCtx`. The
`applyVia`/`applyDirect` branches require `ValValid op` and
`ListValValid args` as inputs because the closure case allocates
args (which requires `EnvValid` on the closure's cenv, which
unfolds from `ValValid` on the closure value).

Status: **fully closed**, including the previously-open `.quote`
and `.set` cases in `eval`. The closure of `.set` involved a
substantive design decision (Path A: restrict `frame`'s domain to
set-free expressions), documented under *Refinements / `.set` and
Path A* below. The closure of `.quote` involved a narrower runtime
restriction on what can appear in a quoted position. Both are
concessions worth flagging — see the corresponding *Refinements*
subsections.

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

- Substrate (`Black.lean`): ~390 LOC (interpreter, primitives,
  initState, evalProgram). Standard, plus the per-prim helper split
  for `applyPrim` (see *Refinements*).
- `Bisim.lean`: ~3300 LOC. Includes the depth-indexed `ValVis_aux` /
  `EnvVis_aux` mutual definition, the universal-depth versions,
  `StateExt` (just policy equality — see *Refinements*) and
  `HeapExt`, validity machinery (`ValValid`, `HeapValid`,
  `EnvValid`), `WFCtx` invariant bundle, two-sided heap-extension
  lemmas (`ValVis_aux_extends`, `EnvVis_aux_extends` mutually
  proved), `ListValVis`, characterization lemmas
  (`ValVis_bool_false_iff`), `applyPrim_bisim` (~600 LOC of per-prim
  case work), `mulConsList_bisim`, `valToList_bisim`,
  `alloc_chain_bisim` (the foldl-induction for closure-call args),
  `EnvVis_cons`, `closure_ValVis_imp_cenv_EnvVis`, and the `frame`
  mutual theorem itself. The framing proof is the bulk; the
  per-prim and foldl helpers are the larger-than-expected pieces.
- `Policies.lean`: ~330 LOC (BlackPolicy, library, structural
  soundness theorems via `split at h`, install-protocol predicates,
  conditional CE soundness for multn).
- LLM cascade glue (`Bedrock.lean` / `Elab.lean` / `Runner.lean` /
  `RunnerMain.lean`): ~600 LOC. Standard Bedrock wrapper +
  spliced-Lean-source elaboration + one-round orchestrator. (Ports
  cleanly from the lean-grey precursor.)

Total: ~4500 LOC at the time of writing, with `.quote`, `.set`, and
the inner trace of `multnExact_CE_nonnum_case` still open. The
framing theorem alone is the bulk: each of the four mutual
functions has many cases, each requiring 30-150 LOC following
established proof templates. The `applyPrim_bisim` and
`alloc_chain_bisim` helpers were ~750 LOC of unanticipated
infrastructure on top of the framing proper.

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

The cross-side state relation between `s_a` and `s_b` is just
**same policy**: `StateExt s_a s_b := s_a.policy = s_b.policy`.
The bilateral same-side heap-monotonicity is captured separately
by `HeapExt s_a s_a' := ∃ extras, s_a'.heap = s_a.heap ++ extras`,
and the cross-side heap relation is implicit through `ValVis` /
`EnvVis` on the relevant values.

Earlier drafts had `StateExt` carry a heap-prefix relation
`∃ extras, s_b.heap = s_a.heap ++ extras` in addition to policy
equality. That part is **provably wrong** as a cross-side *output*
invariant: the closure-call alloc in `applyDirect` allocates `args_a`
on the a-side and the (only `ListValVis`-related) `args_b` on the
b-side, producing `s_a.heap ++ args_a` and `s_b.heap ++ args_b =
s_a.heap ++ extras ++ args_b`. For the result to be in a prefix
relation `s_b'.heap = s_a'.heap ++ extras'`, we'd need
`args_a ++ extras' = extras ++ args_b`, which forces `args_a = args_b`
when `extras = []` — too strong, since `ListValVis` doesn't imply
list equality. The same issue arises in `.letE`, `.app`, `.primApp`.

The bisimulation arguments (`ValVis_extends`, `EnvVis_extends`) all
take *two* extension lists (`ext_a` and `ext_b`) and don't require
them to be related. So the heap-prefix part of `StateExt` was never
load-bearing for framing; it's just policy equality that matters.
Same-policy is preserved by allocation (alloc only changes heap)
and by `installPolicy` symmetrically (both sides install the same
new policy, since framing's `EnvVis metaEnv metaEnv` and the same
`ptable` mean the policy lookup gives matching results).

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
  state_ext : StateExt s_a s_b   -- = (s_a.policy = s_b.policy)
  hv_a, hv_b   : HeapValid s_{a,b}.heap
  ev_a, ev_b   : EnvValid env_{a,b} s_{a,b}.heap
  em_a, em_b   : EnvValid metaEnv s_{a,b}.heap
```

The framing theorem takes `WFCtx` as input and produces `WFCtx` for
the result state.

### `ValValid` outputs and inputs in framing

Two related strengthenings, both needed:

**Outputs** — to chain framing across multi-step recursive cases
(notably `.app`'s 3-step trace: `eval f → evalList args → applyVia`),
the framing conclusion needs to produce `ValValid r_a s_a'.heap` and
`ValValid r_b s_b'.heap` so the result values can be lifted via
`ValVis_extends` into subsequently-extended heaps. The `eval` and
`evalList` branches produce these from `WFCtx`'s heap and env
validity.

**Inputs** — the `applyVia` and `applyDirect` branches *take*
`ValValid op_a/op_b` and `ListValValid args_a/args_b` as
hypotheses. The closure case of `applyDirect` needs them to know
the closure's cenv is `EnvValid` (which is what `ValValid` on a
closure unfolds to) before allocating args — without this, we
can't construct a `WFCtx` for the closure-body call.

The `.app` case of framing satisfies this requirement when calling
`ih_applyVia`: `eval f` produces `ValValid fv_a/fv_b`,
`evalList args` produces `ListValValid avs_a/avs_b`, both lift
across the inner heap extension via `heap_extends`.

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

### `applyPrim_bisim` and the source-level `applyPrim` refactor

Framing's `applyDirect.prim` case needs `applyPrim_bisim`: if
`applyPrim name args_a = some r_a` and `args_a`/`args_b` are
`ListValVis`-related, then `applyPrim name args_b = some r_b` for
some `r_b` with `ValVis r_a r_b`. The proof is per-prim case
analysis (`+`, `-`, `*`, `=`, `mul-list`, predicates, `cons`, `car`,
`cdr`).

The original `applyPrim` definition in `Black.lean` was a single
deeply-nested `match name, args` block covering all 13 prims. Lean's
match compiler **fails to generate equational lemmas** for that
form when `name` is abstract — `simp [applyPrim] at h` doesn't
reduce, blocking the per-prim case analysis. The refactor splits
each prim into its own helper (`applyPrim_plus`, `applyPrim_numQ`,
…) dispatched by `if-else` on `name`. Behavior is identical;
Lean now generates equational lemmas for each helper. This is a
pure source-level change driven by Lean infrastructure friction,
not a design change.

### `alloc_chain_bisim` for closure-call args

Framing's `applyDirect.closure` case allocates `args_a.zip ps` on
one side and `args_b.zip ps` on the other via `foldl`, building up
extended cenvs and heaps. The invariant — the resulting envs and
heaps are `WFCtx`-compatible and `EnvVis`-related — is established
by induction on `args_a` (with `xs_b` and `ps` pinned to matching
length), threading through the per-arg `ValVis_extends`,
`EnvVis_cons`, and validity-extension lemmas. ~150 LOC.

This wasn't anticipated as a separate concern in earlier drafts;
the foldl structure makes it a substantive piece of infrastructure
on its own.

### `.quote` and `closedValB` (closed)

The `.quote v` case requires `ValVis v v` across two different
heaps. For atomic Vals (numbers, booleans, etc.), this is trivial;
for `.cons` and `.closure`, it requires validity hypotheses or a
restriction on what can be quoted.

**Resolution (chosen):** `eval` checks `closedValB v` at the
`.quote v` case and returns `none` if it fails. A "closed" value
is one with no closure references (atoms and cons-trees of atoms);
formally, `closedValB : Val → Bool` traverses the value and rejects
`.closure _ _ _`. The framing case for `.quote` then closes via a
new lemma `closedValB_ValVis_aux : closedValB v = true →
ValVis_aux n v v h_a h_b` proved by induction on `n` and `v`.
Companion lemmas `closedValB_ValValid` and `closedValB_SetFreeVal`
discharge the side validity outputs.

**Concession:** any program that needs to `.quote` a closure-bearing
value will fail at runtime. None of the demos exercise this — the
only `.quote` use in the codebase is `.quote .nilV`. The narrower
alternative (additional hypotheses on `frame` rather than narrowing
`eval`) was rejected as more invasive: it would have required
threading a `ValValid v` hypothesis through every `frame.eval`
recursive case, where `.quote` only appears as a leaf.

### `.set` and Path A (closed)

The `.set` case in framing involves the meta-mutation policy gate:
when a `set!` targets a meta-env binding, `s.policy oldVal newVal`
decides whether to admit the mutation, and on admission the heap
is updated *in place* via `Heap.update idx v`.

Earlier drafts of this section identified one obstacle: `s.policy`
is a black-box `Bool`-valued function, so it can return different
verdicts on `ValVis`-related-but-unequal inputs across the two
sides of the bisimulation. Working through the closure surfaced a
second, deeper obstacle: the framing-theorem postcondition includes
`HeapExt s_a s_a' := ∃ extras, s_a'.heap = s_a.heap ++ extras`, and
in-place `Heap.update` is *not* a prefix extension. So the
postcondition is unprovable for the `.set`-accepted branch
*regardless* of policy-respect.

A still-deeper observation: even if both obstacles were addressed
by adding a `BisimSafe` policy hypothesis (admit only `ValVis`-
related transitions) and by weakening `HeapExt` to a `HeapEvolves`
relation that admits bisim-respecting updates — *the resulting
theorem would not apply to `multnExactPolicy`*, because
`multnExactPolicy` admits replacing `.builtinBaseApply` (a tag
constructor) with a `.closure` value (a different constructor),
which are operationally CE-equivalent but structurally non-
`ValVis`-related by inversion. The very policies that make
reflective mutation interesting cannot satisfy `BisimSafe`.

The deeper truth: a *structural* framing theorem across reflective
`.set` is incoherent in this language. `ValVis` is syntactic data
refinement (Kumar 2016 §3.2); `CE` is operational; reflective
mutation is, by design, an operational substitution.

**Resolution (chosen): Path A — set-free framing.** Add three new
predicates:

- `SetFreeExpr : Expr → Prop` — recursively true except at `.set _ _`.
- `SetFreeVal : Val → Prop` — heap-independent; for closures, body is
  `SetFreeExpr`.
- `HeapSetFree : Heap → Prop` — every cell holds a `SetFreeVal`.

Thread them through the four mutual statements of `frame`: take
`SetFreeExpr` / `SetFreeListExpr` on the source-side of `eval` /
`evalList`, `SetFreeVal` / `SetFreeListVal` on `applyVia` /
`applyDirect`'s op and args, and add `HeapSetFree` on both sides
to `WFCtx`. The `.set _ _` case of `frame.eval` then closes by
contradiction from `SetFreeExpr (.set _ _) = False`.

The design space considered before settling on Path A:

- **Path A** — set-free framing (chosen). Restrict `frame`'s
  domain via `SetFreeExpr` / `SetFreeVal` / `HeapSetFree`. The
  reflective `.set` step lives outside `frame`. The install-
  protocol theorem (`multnExact_soundForCE_first_install`) uses
  `frame.applyDirect` only on the post-install user-call, where
  no `.set` appears.
- **Path B** — `BisimSafe`-restricted `.set` framing. Define
  `BlackPolicy.BisimSafe := ∀ old new h, p old new = true → ∀ n,
  ValVis_aux n old new h h` and add it as a hypothesis to
  `WFCtx`. Define `HeapEvolves` (admits append + bisim-safe
  in-place update) and replace `HeapExt` in `frame`'s
  postcondition. `multnExactPolicy` is *not* `BisimSafe` — it
  admits `(.builtinBaseApply, .closure ...)` which differ in
  constructor — so this lemma, while clean and general, has no
  client in this development. Estimated ~500 LOC of new
  infrastructure.
- **Path A + B** — both. Path A as the working framing for
  `multnExact_soundForCE_first_install`; Path B as a textbook
  companion for hypothetical structural-extension policies.
  Highest LOC, no operational gain over Path A alone for the
  current development.

Path A is the operationally honest answer for this language:
framing covers the non-reflective sublanguage, and reflective
`.set` steps are covered separately by the install-protocol
theorems (`multnExact_soundForCE_first_install` and its kin).

**Concession:** `frame` no longer applies to expressions containing
`.set`. Reflective mutation steps must be handled outside `frame`,
which is exactly what the install-protocol theorems already do.
`multnExact_soundForCE_first_install` now takes three additional
hypotheses — `HeapSetFree s.heap`, `SetFreeVal op`,
`SetFreeListVal operands` — that the runner trivially maintains.

## Risks

- **Sub-cases in framing were tedious.** Each function in the mutual
  block has many cases (`eval` has 13). The pattern is uniform but
  verbose. The framing theorem is now fully closed; the closure
  case of `applyDirect` was harder than this risk initially
  anticipated — it needs `alloc_chain_bisim`, an inductive proof
  over `args.zip ps` that wasn't obvious from the initial sketch.

- **`match`-equational-lemma generation is brittle.** Lean 4's match
  compiler doesn't always generate equational lemmas for deeply-
  nested patterns. The original `applyPrim` definition (one big
  `match name, args`) hit this and required a source-level refactor
  to per-prim helpers. Future cases that need to reason about
  large abstract `match` expressions may need similar refactoring.

- **Closure's body-equality requirement might be too strong.** The
  framing requires `body_a = body_b` for closures to relate. If the
  closures we hand to `applyDirect` are produced by *different*
  evaluations, their bodies are equal (we're not compiling), so this
  should hold automatically.

- **Path-A side-conditions must be maintained by the runner.** The
  framing-theorem domain restriction documented under *Refinements
  / `.set` and Path A* requires that `multnExact_soundForCE_first_install`
  callers establish `HeapSetFree s.heap`, `SetFreeVal op`, and
  `SetFreeListVal operands`. The runner trivially maintains these
  in practice (it constructs values only from `.lam` bodies of
  set-free Black source and atomic literals), but a future
  extension that allows storing closures with `.set`-bearing
  bodies in heap-resident cells would have to either (a) ensure
  those closures aren't passed as user ops to `applyDirect`, or
  (b) re-extend `frame` along Path B lines (with the caveat that
  the Path B lemma cannot apply to non-`BisimSafe` policies like
  `multnExactPolicy`).

- **The two-stage proof split is now a load-bearing architectural
  commitment.** Framing covers the non-reflective sublanguage;
  reflective `.set` steps are covered by install-protocol
  theorems. This split is principled (a structural framing theorem
  across reflective `.set` is *provably false* for the policies
  that make reflection interesting), but the codebase no longer
  has a single "the framing theorem" applicable to all programs.
  Any future development that wants a uniform framing claim across
  reflective steps would have to revisit the architectural
  decision recorded under *Refinements / `.set` and Path A*.

The first three are sequencing or implementation risks; the last
two are concession-tracking entries — they record commitments the
build made when closing `.set` and `.quote`, not open issues.

## References

- [`docs/Kumar_2016_thesis.pdf`](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-879.html) — primary inspiration. Chapter 2
  (shallow→deep translation, refinement invariants), Chapter 3
  (verified compiler, data refinement for closures, fuel-based
  divergence preservation).
- [`docs/CakeML_Kumar_2014.pdf`](https://dl.acm.org/doi/10.1145/2578855.2535841) — the foundational POPL paper.
- [`cakeml/compiler/scheme/`](https://github.com/CakeML/cakeml/tree/master/compiler/scheme) — verified Scheme-to-CakeML compiler
  in HOL4. Source semantics (`scheme_semanticsScript.sml`) is
  structurally close to lean-black's (value type with closures and
  pairs, store with `Mut`/`Pair` entries, `fresh_loc` allocation).
  Useful as a concrete reference for value/env/store handling.
- [`black/black.scm`](https://github.com/readevalprintlove/black/blob/master/black.scm) — Asai et al.'s reference implementation of
  Black. lean-black is a Lean 4 reimplementation of the core
  reflective architecture.

# lean-green — future directions

The current development closes a single end-to-end story:
`multnExactPolicy` is conservative-extension-sound on the first
admitted install from a clean state. Closing this exposed the
right shape of the framing problem (Path A: framing covers the
non-reflective sublanguage; reflective steps are install-protocol
theorems composing framing on the post-install user-call). What
follows are directions that could extend, sharpen, or rewrite the
result. They split into three families: *extending the verified
story*, *generalizing the infrastructure*, and *redoing it on
different foundations*.

---

## Extending the verified story

### Multi-install soundness

Currently `multnExact_soundForCE_first_install` covers exactly
*one* admission from a clean state. A real reflective interpreter
admits a sequence of modifications, each in a state where
previous admissions have already mutated the meta-env. The
generalization:

```
multnExact_soundForCE_seq :
  -- given a chain of admitted installs and the resulting state,
  -- the post-chain `callAsBaseApply` CE-extends the pre-chain one
  ...
```

The hard part is not the framing (each individual install is
covered by Path A on the post-install user-call). It is keeping
the install-protocol invariants — `OrigBoundIn`, `NumQBoundIn` —
inductive across the chain. After install₁, what does
`OrigBoundIn` say about install₂'s captured `orig`? It captures
*the post-install₁* `base-apply`, which is the install₁ closure,
not `.builtinBaseApply`. So the install-protocol predicates have
to be parameterized by what `orig` captures, with a proof that
the captured value CE-extends `.builtinBaseApply` (transitively
through the install chain).

Estimated: a new `InstallChain` predicate + an inductive proof
that each chain step preserves CE-soundness. ~300 LOC.

### CE-soundness for `numGuardPolicy`

`numGuardPolicy` is in `verifiedTable` with structural soundness
(it admits exactly closures matching the syntactic shape) but
*no* operational CE-soundness theorem. A `numGuard_soundForCE` —
analogous to `multnExact_soundForCE_first_install` but for the
looser shape — would round out the table.

The catch: `numGuardPolicy` permits closures whose else-branch is
unconstrained. CE-soundness for `numGuardPolicy` *can't hold* in
general — a malicious closure matching the shape with a
constant-returning else-branch breaks CE on non-numeric operators.
So either:
- restrict the table to admit only `numGuardPolicy`-shapes that
  *additionally* delegate to `orig` in the else-branch (which
  recovers `multnExactPolicy`), or
- weaken the architectural floor for `numGuardPolicy` from `CE`
  to something it actually preserves (e.g. `CE_on_numeric`).

The second option is the more interesting research direction:
*per-policy* architectural floors. Today the table assumes one
common `P`. A future table would carry, per entry, the floor each
policy is sound for, with a meet-of-floors describing the table's
combined guarantee.

### A richer policy library

Three policies worth adding:
- **Type-respecting**: admit only modifications whose proposed
  closure has the same arity / argument shapes / return shape as
  the value it replaces. Requires lifting "shape" to a Lean-level
  predicate over `Val`.
- **Capability-bounded**: admit only modifications whose captured
  cenv contains a subset of "allowed" names (e.g., no
  `base-apply`, only `num?` and `orig`). Trivially decidable on
  the cenv structure.
- **Proof-carrying**: admit a modification only when accompanied
  by a closed `Lean` proof term of CE-soundness. The runner
  type-checks the proof (via `Elab.lean`'s elaboration path)
  before admitting. The interesting design question is how to
  represent "the proposed closure CE-extends `old`" as a Lean
  goal that the LLM can plausibly synthesize.

The proof-carrying option re-frames the LLM's role: it generates
not just *programs* but *programs + soundness proofs*. The gate
becomes a proof-checker. This is the cleanest route to "the LLM
cannot bypass the gate" being a pure type-theoretic property.

### Wider runtime invariants (kill the Path-A side-conditions)

The headline theorem currently takes `SetFreeWF` as an explicit
side-condition. A natural extension: prove that the *runner* itself
preserves `HeapSetFree` / `SetFreeVal` across any sequence of
admissions, given that the initial state is set-free and every
admission is from set-free Black source. With that meta-theorem,
callers of `multnExact_soundForCE_first_install` can discharge
`SetFreeWF` once at runner-startup.

This is the "concession 2" practical-impact paragraph in the
README, made formal: the runner's set-free invariant becomes a
proved property, not a precondition.

### Extending Path A to admit a Path-A-compatible class of `.set`

Path A excludes all `.set` from `frame`'s domain. But not all
`.set` is reflective: `(.set x e)` where `x` is a *non*-meta
binding doesn't go through the policy gate (the `else` branch in
`eval`'s `.set` clause). Plain mutation does mutate the heap, but
the new value is whatever `e` evaluates to — and if `e` is
set-free, the new value is `SetFreeVal`, so `HeapSetFree` is
preserved.

So Path A could be extended to admit *non-meta* `.set`. The
restriction would be: `frame` rejects `.set x e` only when
`isMetaMutation x env metaEnv = true`, which is a runtime check.
Encoding this as a syntactic predicate is possible if we carry the
metaEnv through `SetFreeExpr`'s definition.

Practical payoff: probably small. Black programs in this
development don't use plain `.set`. But it would tighten the
"Path A is *exactly* the non-reflective sublanguage" claim to
"Path A is *exactly* the not-meta-mutating sublanguage."

---

## Generalizing the infrastructure

### Path B as a companion theorem

The README's *Concessions* section argues Path B (a `BisimSafe`-
restricted framing across `.set`) doesn't help any current
client because `multnExactPolicy` isn't `BisimSafe`. But Path B
*as a textbook framing theorem* is still worth having. Future
policies — type-respecting policies, structurally-extending
policies — could be `BisimSafe` and benefit from a single,
uniform `frame_bisimsafe` theorem.

Sketch:

```
def BlackPolicy.BisimSafe (p : BlackPolicy) : Prop :=
  ∀ old new h, p old new = true → ∀ n, ValVis_aux n old new h h

def HeapEvolves (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧
  ∀ i v, h[i]? = some v →
    ∃ v', h'[i]? = some v' ∧ ∀ n, ValVis_aux n v v' h h'

theorem frame_bisimsafe : ∀ n, FrameStmt_bisimsafe n
```

`FrameStmt_bisimsafe` replaces `HeapExt` with `HeapEvolves` in the
postcondition and adds `BlackPolicy.BisimSafe` as a hypothesis on
the policy. The `.set` case closes via `HeapEvolves.update` once
the policy admits.

Estimated: ~500 LOC of new infrastructure (HeapEvolves +
`ValVis_aux_evolves` + `EnvVis_aux_evolves` + the `.set` proof).

### Bundle the per-side `frame` hypotheses

`frame.applyDirect` takes 13 hypotheses including four pairs of
"left-side / right-side" facts (`ValValid op_a` / `ValValid op_b`,
etc.). A `WFVal v h := ValValid v h ∧ SetFreeVal v` and
`WFList vs h := ListValValid vs h ∧ SetFreeListVal vs` would
collapse those pairs into single fields, halving the visible
hypothesis count. The proof body would destructure at IH callsites
— a wash on internal LOC, but a real win on signature legibility.

### Replace `HeapExt` with the universal `HeapEvolves`

Even within Path A, `HeapExt`'s prefix-shape forces several
compose-and-destructure-and-recompose dances in `frame`. The
fully-monotonic `HeapEvolves` (which subsumes `HeapExt` and
incidentally enables Path B) would simplify these. Worth doing
even without Path B, just for cleanup.

### Decompose `Bisim.lean`

`Bisim.lean` is ~3500 LOC in one file. Natural splits:
- `Bisim/ValVis.lean` — `ValVis_aux` / `EnvVis_aux` definitions
  and basic lemmas.
- `Bisim/Validity.lean` — `ValValid` / `HeapValid` / `EnvValid`
  + extension lemmas.
- `Bisim/SetFree.lean` — `SetFreeExpr` / `SetFreeVal` /
  `HeapSetFree` + preservation lemmas.
- `Bisim/Closed.lean` — `closedValB` + reflexivity lemmas.
- `Bisim/PrimBisim.lean` — `applyPrim_bisim` (the ~600 LOC piece).
- `Bisim/AllocChain.lean` — `alloc_chain_bisim`.
- `Bisim/Frame.lean` — `WFCtx` + `FrameStmt` + the 1500-line
  `frame` proof itself.

The `frame` mutual-induction structure forces some interleaving,
but the file split is worth it for incremental compilation alone.

### Migrate to Mathlib

The development is currently mathlib-free, by choice (small
toolchain footprint for the LICS keynote demo). A mathlib-based
rewrite would replace ad-hoc list lemmas with `List.foldl`-
manipulation tactics, cleaner `getElem?` reasoning, and possibly
the `bisim` machinery in `Mathlib.Logic.Relation`. Estimated:
substantial rewrite, modest LOC reduction (~20%), real
maintainability win.

---

## Redoing it on different foundations

### Coinductive evaluation, no fuel

Fuel-indexed evaluation forces every framing claim to thread fuel
through the proof, and the headline theorem to take `fuel ≥ 2` as
a side-condition. A coinductive trace semantics —
`Coeval : Expr → Env → Heap → CoTrace`, with `CoTrace` capturing
diverging traces as well as terminating ones — eliminates fuel
from the surface of the proof. The framing claim becomes
"bisim-related inputs produce bisim-related coevaluation traces."

This is closer to Black's actual operational character (where
non-termination is a meaningful possibility, not a fuel ran out).
Trade-off: coinductive proofs in Lean 4 are workable but
significantly less ergonomic than induction-on-fuel.

### Logical relations instead of CakeML-style `ValVis`

`ValVis` is syntax-based data refinement: closures relate iff
*bodies are syntactically equal*. This is the right relation when
source and target are the same language and we're proving fuel
bisimulation. It is *not* the right relation for compiler-style
correctness (where source body and target body differ) or for
program equivalence (where two algorithmically distinct closures
should relate iff they implement the same function).

A step-indexed logical relation —
`V[T] v_a v_b ≜ ∀ args ∈ V[Args], E[T_ret] (apply v_a args) (apply v_b args)` —
would relate operationally-equivalent closures regardless of
syntactic shape. The CE relation defined operationally on
`callAsBaseApply` is already this shape; lifting it to a closed
logical relation would let the framing theorem cover
operationally-equivalent installs (which is exactly what the
*Concessions* section argued was unprovable structurally).

This is the deepest follow-up. It would make Path A's set-free
restriction unnecessary: a logical-relations framing theorem
would handle reflective `.set` on operationally-CE policies
*including* `multnExactPolicy`. Estimated: a major redo, several
thousand LOC, and a much stronger end result.

### Mechanize Black's full meta-tower

Black's reflective architecture has *infinite* meta-levels: the
meta-env's meta-env has its own meta-env, and so on. The current
development collapses this to two levels (base + one meta). A
faithful mechanization would represent the tower and prove the
"reflection collapses past one level" theorem (every program's
behavior depends on at most a finite prefix of the tower).

Black's paper handles this via lazy meta-level construction; a
Lean mechanization would need a `MetaTower : Nat → Env` indexed
family + a proof that any terminating program's evaluation looks
at finitely many indices. This is the most "Black-faithful"
extension — and the one that would make the development a
candidate for a real publication on reflective interpreter
verification rather than a keynote demo.

### Cross-language framing (Black source → ?)

A compilation pass — Black source to a simpler IR or to JIT
emit — paired with a compiler-correctness proof using the
existing `frame` infrastructure. The compiler's correctness would
say: source-level `eval` and target-level `eval` are bisim-related
across the compilation. This is exactly the setting Kumar 2016
addressed for CakeML; this development's `ValVis` is essentially
the right relation for it.

Concrete near-target: compile the `.primApp f args` form to
direct-dispatch (skipping the `applyVia` indirection through
`metaEnv.lookup "base-apply"`) when `f` is a known-prim. The
compilation correctness theorem mirrors `frame.primApp` with the
target's direct-dispatch eval on the right side.

---

## LLM-cascade extensions

### Stage proposals + their soundness proofs

The current `runner` proposes Black-source modifications and
admits/rejects them under the active policy. A natural extension:
the LLM proposes *both* a modification and a Lean proof of its
CE-soundness; the runner type-checks the proof. This converts the
gate from a structural pattern-matcher into a proof-checker (see
*A richer policy library / Proof-carrying* above).

The interaction loop would look like:
1. Runner shows LLM the current state + admitted modifications +
   the architectural floor `P`.
2. LLM proposes `(modification, soundness-proof-tactic-script)`.
3. Runner elaborates both, runs the tactic, checks it produces a
   closed term of `P old new`.
4. Admit if both elaborate; reject otherwise.

The hard part is making the proof obligation tractable for the
LLM. CE-soundness proofs are non-trivial — `multnExact_CE_nonnum_case`
is ~100 lines. A pragmatic approximation: provide a high-level
tactic `mt_attempt_ce_soundness` that handles the common cases
(structural-shape policies that delegate to `orig`); the LLM only
has to write the policy-specific arguments.

### Multi-round proposal compounding

Currently `runner [N]` does N independent rounds; admitted
proposals accumulate as context for subsequent rounds, but each
round's proposal is independent. A richer cascade would let the
LLM propose *compositions*: "given installed modification A,
propose B such that the composition CE-extends `.builtinBaseApply`
through both." The soundness theorem would chain
`multnExact_soundForCE_first_install`-style lemmas.

This is the test case for *Multi-install soundness* above.

### Replay / counterexample search

Track the rejected proposals across runs and use them to
fine-tune the LLM's search space. Adversarially: have one LLM
propose modifications and another propose breakages
(non-CE-extending modifications that match the structural shape),
and use the proof-checker to adjudicate. The proof-checker
constraint ensures the adversarial loop converges on
*structurally-shaped-but-non-CE* boundary cases, which would map
out the "policy is too loose" failures of `numGuardPolicy`.

---

## Reorganization sketches

### One-file inline mode

For the LICS keynote demo, the development could live in a single
self-contained `.lean` file ~5000 lines, no `lake` build, no
imports beyond `Init` / `Std`. Splitting concerns into `Bisim` /
`Policies` / `Black` makes maintenance easier but reading
sequence harder. A "demo-first" inline form would make the talk
follow the source.

### Two-file split: kernel vs. cascade

The `Bisim.lean` + `Policies.lean` + `Black.lean` files form a
self-contained kernel — they prove `multnExact_soundForCE_first_install`
without any LLM dependency. The `Bedrock.lean` + `Elab.lean` +
`Runner.lean` files form the LLM cascade. Splitting these into
two repos / two `lake` packages would let the kernel be cited as
a verified-policies-library and let the cascade be cited as a
LLM-proposer-architecture, independently.

### `lean-green` → `lean-black-2`

The repo is named `lean-green` because it's the second iteration
of `lean-black`. The first iteration's lessons (refinements
documented under DESIGN.md / *Refinements*) all influenced this
iteration's design. A natural third iteration —
`lean-blue`? `lean-black-2`? — could start fresh with the Path A /
Path B / logical-relations design space mapped out, choosing the
trade-off that fits the next stage of the project's ambitions.

---

## What this isn't (yet)

A few things explicitly out of scope at the current stage:
- A *machine-checked* runner. The runner is Lean 4 code that
  shells out to AWS, but the *Lean* portion of the runner isn't
  proved correct against the spec. (The kernel is proved against
  the spec; the kernel is what runs *inside* `Smoke.lean`.)
- Concurrency. Black's reflective architecture is sequential; a
  concurrent extension would need a separate story for atomicity
  of meta-mutation.
- Garbage collection. The heap grows monotonically; no claim
  about reclamation.
- A non-`lake env lean --run`-based elaborator. The proposal
  elaboration path hard-codes the spawn shape; replacing it with
  a faster in-process elaborator would change the cascade
  performance characteristics but not the verified guarantees.

# lean-green — future directions

The current development closes a single end-to-end story:
`multnExactPolicy` is conservative-extension-sound on the first
admitted install from a clean state. The framing infrastructure
that makes the proof go through is closed *modulo* the `.set`
case of `frame.eval`, which remains an open `sorry`. Routes for
extending, sharpening, or rewriting the result split into three
families: *extending the verified story*, *generalizing the
infrastructure* (including closing the `.set` case), and *redoing
it on different foundations*.

---

## Hardening the proposal-to-admission seam

Items 1, 3, and 6 of this roadmap have **landed**. Items 2, 4,
5, and 7 remain.

The original gap, as the README's *Concession 0* notes:
`multnExact_soundForCE_first_install` requires install-protocol
facts (`InstallFacts`: `OrigBoundIn`, `NumQBoundIn`) that the
runtime gate originally couldn't inspect, and the runner admits
under `numGuardPolicy` (loose, not CE-sound) rather than
`multnExactPolicy`.

### 1. ✅ DONE — Freeze `s.policy` before evaluating `.set`'s RHS

`Black.lean`'s `.set` now snapshots `gate := s.policy` before
evaluating `e`, then checks `gate ctx oldVal v` after `e`
completes. `installPolicy` calls inside `e` still take effect
post-`.set` but don't authorize the current `.set`. Tested in
`Smoke.lean` scene 3 (`test_strict_freeze_admits_install`,
`test_strict_freeze_post_install_locked`). See `GOTCHAS.md` #1.

### 2. Restrict admissible proposals to direct `.lam` syntax

The trusted installer should accept only

```
.lam ["op", "args"] body
```

— not arbitrary `Expr` that happens to evaluate to a closure.
With item 3 landed, the runtime's `multnExactPolicy` *already*
catches the shadowed-`orig` attack via the `OrigBoundIn` check,
so the practical risk is reduced. But syntactic restriction at
the elaboration layer is still a defense-in-depth win, and it
rules out `.set`-ful preludes in the RHS that item 1 doesn't
address.

Concretely: replace the LLM's "any Black `Expr`" interface with
a "Lean-checked `body` expression" interface; the installer
wraps it in `.lam` against the trusted Black runtime's `cenv`
(which actually holds `base-apply` = the previous gate).

### 3. ✅ DONE — Extend `BlackPolicy` to take a `MutationCtx`

`BlackPolicy` is now `MutationCtx → Val → Val → Bool`. The ctx
carries the target name, heap, env, metaEnv, and index.
`multnExactPolicy` checks `ctx.target = "base-apply"` *and*
verifies `OrigBoundIn` (closure cenv binds `"orig"` to a heap
cell holding `.builtinBaseApply`) *and* `NumQBoundIn` (cenv
binds `"num?"` to `.prim "num?"`) against the live heap.

The bridge lemma `multnExactPolicy_implies_InstallFacts` proves
that runtime admission discharges exactly the install-protocol
facts the headline theorem requires. Tested in `Smoke.lean`
scene 3 — shadowed-`orig`, wrong target, `numGuard`-shaped
malicious all refused.

### 4. Switch the runner to `multnExactPolicy` + a trusted installer

With (1) and (3) landed, this is now mostly a config flip in
`Elab.lean` (`installPolicy 1` → `installPolicy 2` for
`idx_multnExact`) plus an updated prompt in `Runner.lean`. The
trusted installer can stay as a thin wrapper that just calls
`(em (let orig base-apply (set! base-apply <PROP>)))`; the
runtime gate will now actually enforce the install-protocol
facts.

### 5. Strengthen `CE` with post-state conditions

The current `CE` says "old succeeds → new succeeds with a
`ValVis`-related result." It does not say the result *states*
agree on policy, on heap-validity, or on the `base-apply` cell's
contents. A reflective replacement could preserve the immediate
result while corrupting future dispatch. Strengthen `CE` to:

```lean
def CE (old new : Val) : Prop :=
  ∀ ..., callAsBaseApply ... old ... = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply ... new ... = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap ∧
      s'.policy = s''.policy ∧               -- policy preserved
      HeapValid s''.heap ∧                   -- heap invariant preserved
      s''.heap.length ≥ s'.heap.length       -- monotone
```

The existing `frame.applyDirect` already returns most of this in
its postcondition — wiring it through to `CE` is mostly
plumbing, not new theorem work. Either rename the current
property to `CE_oneCallResult` and reserve `CE` for the
strengthened version, or strengthen in place and update the
headline theorem accordingly.

### 6. ✅ DONE — Adversarial smoke tests + non-zero CI exit

`Smoke.lean` exits non-zero on failure and includes scene 3
("strict-governed + adversarial") with seven tests under
`multnExactPolicy`:

- multn install admitted, `(+ 1 2) ⇒ 3` preserved.
- `numGuard`-shaped malicious wrapper refused (shape doesn't
  match strict multn pattern).
- Shadowed-`orig` wrapper refused (runtime `OrigBoundIn` check).
- TOCTOU `installPolicy`-mid-RHS: install proceeds under the
  frozen pre-RHS gate; subsequent mutations locked by the
  downgrade that took effect post-`.set`.
- Wrong target (`+` instead of `base-apply`) refused (runtime
  `target = "base-apply"` check).

Two adversarial cases not yet exercised: proposal with `.em`
nesting, and `.set`-ful prelude in RHS before the canonical
`.lam`. Both are mostly defense-in-depth — the current
`multnExactPolicy` already catches the resulting shapes — but
adding them as explicit smoke entries would complete the
adversarial coverage.

### 7. Sandbox the proposal elaboration path

`Elab.lean` writes LLM output into a Lean source file and runs
`lake env lean --run`, which is effectively executing untrusted
Lean. The prompt's "no commentary" instruction is not a
security boundary. Three options, in increasing order of
isolation:

- **Black `Expr` parser**: have the LLM emit a string in a small
  Black-source notation, parsed by a Lean function in `Black.lean`.
  Eliminates Lean elaboration-time side effects entirely.
- **JSON AST**: the LLM emits a JSON form of `Expr`; deserialize
  to `Expr` directly.
- **Sandboxed elaboration**: keep the current shape but run
  `lake env lean --run` in a process with no credentials, no
  network, read-only repo, and a private temp directory.

The first two are the right long-term answer; the third is a
mitigation that lets the current cascade run more safely while
the parser/AST route is built.

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

The hard part is not the framing (each individual install's
post-call is set-free, so `frame.applyDirect` applies). It is
keeping
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

---

## Generalizing the infrastructure

### Closing `frame.eval`'s `.set` case via `HeapEvolves`

This is the open `sorry` in `Bisim.lean`. Two things are needed:

**(a) Replace `HeapExt` with `HeapEvolves`.** `HeapExt s_a s_a' :=
∃ extras, s_a'.heap = s_a.heap ++ extras` is a *prefix*-extension
relation; in-place `Heap.update` (the `.set`-accepted branch's
heap mutation) violates it because the new heap has the same
length but differs at one index. Weaken to:

```
def HeapEvolves (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧
  ∀ i v, h[i]? = some v →
    ∃ v', h'[i]? = some v' ∧ ∀ n, ValVis_aux n v v' h h'
```

— heap may grow, *and* old indices may be updated, provided the
new value at each old index is bisim-related to the old. Prove
`ValVis_aux_evolves` and `EnvVis_aux_evolves` (depth-induction)
and replace `HeapExt` in `frame`'s postcondition.

**(b) Add a *policy-respecting-bisim* hypothesis to `WFCtx`:**

```
∀ x_a x_b y_a y_b, ValVis x_a x_b → ValVis y_a y_b →
  s.policy x_a y_a = s.policy x_b y_b
```

— the policy gives the same answer on bisim-related inputs.
This is satisfied by every policy in `verifiedTable` (each
pattern-matches on shape, and `ValVis` on closures requires body
equality, so shape is preserved). The `.set` case of `frame.eval`
then closes: both sides decide the same way; both either reject
(heap unchanged, trivially `HeapEvolves`) or admit with bisim-
related new values (a single `HeapEvolves.update` step).

Estimated cost: ~500 LOC of new infrastructure (`HeapEvolves`
definition and lemmas, the two `_evolves` framing lemmas, the
`WFCtx` extension, and the `.set` proof itself). Replacing
`HeapExt` ripples through ~30 sites in `frame`'s proof.

**Why not `BisimSafe`?** A briefly-considered stronger condition
was `BisimSafe(p) := ∀ old new h, p old new = true → ∀ n,
ValVis_aux n old new h h`. `multnExactPolicy` does *not* satisfy
this: it admits `(.builtinBaseApply, .closure ...)`, which are
different `Val` constructors and so not bisim-related. The
*policy-respecting-bisim* condition above is the weaker, satisfied
condition. Any uniform-framing-across-`.set` follow-up should use
the weaker condition; an earlier draft of the docs conflated the
two.

### Bundle the per-side `frame` hypotheses

`frame.applyDirect` takes pairs of "left-side / right-side" facts
(`ValValid op_a` / `ValValid op_b`, `ListValValid args_a` /
`ListValValid args_b`, etc.). A `WFVal v h := ValValid v h ∧ ...`
and `WFList vs h := ListValValid vs h ∧ ...` would collapse those
pairs into single fields, halving the visible hypothesis count.
The proof body would destructure at IH callsites — a wash on
internal LOC, but a real win on signature legibility.

### Decompose `Bisim.lean`

`Bisim.lean` is ~3300 LOC in one file. Natural splits:
- `Bisim/ValVis.lean` — `ValVis_aux` / `EnvVis_aux` definitions
  and basic lemmas.
- `Bisim/Validity.lean` — `ValValid` / `HeapValid` / `EnvValid`
  + extension lemmas.
- `Bisim/Closed.lean` — `closedValB` + reflexivity lemmas.
- `Bisim/PrimBisim.lean` — `applyPrim_bisim` (the ~600 LOC piece).
- `Bisim/AllocChain.lean` — `alloc_chain_bisim`.
- `Bisim/Frame.lean` — `WFCtx` + `FrameStmt` + the `frame` proof
  itself.

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
operationally-equivalent installs.

This is the deepest follow-up. It would let `frame` handle
reflective `.set` on operationally-CE policies *including*
`multnExactPolicy` (where structural `ValVis` between
`.builtinBaseApply` and a multn closure is `False` by inversion).
Estimated: a major redo, several thousand LOC, and a much
stronger end result. Versus the `HeapEvolves` follow-up
(generalizing the infrastructure / closing the `.set` case),
this is more general but also much more work — `HeapEvolves`
already gets framing-across-`.set` for the policies in
`verifiedTable` since they all satisfy policy-respecting-bisim;
logical relations would add coverage for hypothetical policies
where the policy itself would need a behavioral specification.

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
`lean-blue`? `lean-black-2`? — could start fresh with the
`HeapEvolves`-vs-logical-relations design space mapped out,
choosing the trade-off that fits the next stage of the project's
ambitions.

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

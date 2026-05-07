# lean-green — future directions

The current development closes a single end-to-end story:
`multnExactPolicy` is conservative-extension-sound on the first
admitted install from a clean state. **The framing infrastructure
is fully closed, including the `.set` case of `frame.eval`** (via
the cross-side `HeapEvolution` + `PolicyRespectsBisim` architecture
documented below). Routes for extending, sharpening, or rewriting
the result split into three families: *extending the verified
story*, *generalizing the infrastructure*, and *redoing it on
different foundations*.

A single `sorry` remains in `Policies.lean` — see *Outstanding
sorry* below.

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

### 2. ✅ DONE — Restrict admissible proposals to direct `.lam` syntax

`Elab.lean`'s wrapper now syntactically checks the proposal:

```lean
def isWellFormedProposal : Expr → Bool
  | .lam ["op", "args"] _ => true
  | _                     => false
```

Anything other than exactly `.lam ["op", "args"] body` is
rejected before the install. This rules out `.set`-ful preludes,
nested `.em`, `seq`-with-installPolicy, and other classes of
attack that operate at the elaboration layer (rather than via
the runtime gate). The runtime gate's `OrigBoundIn` check
catches semantic violations; the syntactic check catches
structural ones. Defense-in-depth — both layers active.

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

### 4. ✅ DONE — Switch the runner to `multnExactPolicy`

`Elab.lean` now hardcodes `installPolicy 2` (`idx_multnExact`).
`Runner.lean`'s prompt describes the strict shape and the
runtime install-protocol checks. The trusted installer is the
thin wrapper `(em (let orig base-apply (set! base-apply <PROP>)))`;
the runtime gate now actually enforces target / shape /
`OrigBoundIn` / `NumQBoundIn` via `MutationCtx`.

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

### Multi-install soundness (runtime done, proof partial)

A real reflective interpreter admits a sequence of modifications,
not just one. Generalizing single-install CE soundness to a
chain-CE theorem is partway done.

**What's already in place** (committed):
- **Runtime gate is multi-install ready.** `multnExactPolicy` is
  `oldVal`-parametric: it admits a multn-shape closure whose
  captured `orig` cell holds *whatever value is currently at
  `base-apply`*, not specifically `.builtinBaseApply`. First
  install: `oldVal = .builtinBaseApply`. Second install:
  `oldVal = M₁` (the first install's closure). The `Val.beq`
  / `Expr.beq` / `Env.beq` mutual structural equality machinery
  in `Black.lean` powers this, and `val_beq_eq` lifts it to a
  propositional equality the bridge lemma uses.
- **Bridge lemma is parametric.** `multnExactPolicy_implies_InstallFacts`
  produces `InstallFacts oldVal new ctx.heap` for any `oldVal`,
  not just the first-install case.
- **Smoke verifies multi-install end-to-end.** Scene 3's
  `multi-install (M₂ ∘ M₁)` test runs two consecutive installs
  under `multnExactPolicy` and confirms `(2 3 4) ⇒ 24` survives
  the chain.

**What remains** (the proof side):
- The headline `multnExact_soundForCE_first_install` theorem
  still hardcodes `oldVal = .builtinBaseApply` in the call shape:
  the `callAsBaseApply ... .builtinBaseApply ... = some (r, s')`
  hypothesis assumes the old call goes through the builtin
  dispatcher. For chain CE, the old call could go through a
  closure (the previous multn). Generalizing the proof requires
  handling the closure-dispatch path through `applyDirect baseApply
  [op, listToVal operands]`.
- `CE.refl` and `CE.trans` — both need `ValVis` and `EnvVis`
  transitivity lemmas (`ValVis_aux_trans` / `EnvVis_aux_trans`,
  mutually recursive at every depth). These are the substantive
  proof work.
- Compose the chain theorem: each install proves CE between the
  new closure and the previous; chain transitivity gives CE back
  to `.builtinBaseApply`. ~50 LOC once the lemmas above are in
  place.

**On the difficulty.** Attempted `ValVis_aux_trans` twice in a
session and bailed each time. The structure is right (mutual
induction at every depth `n`, with `EnvVis_aux_trans` at depth
`n` calling `ValVis_aux_trans` at depth `n-1`), but the case
analysis over `Val`-constructor triples (`v_a × v_b × v_c`) is
8³ = 512 combinations to dispatch — most are mismatches that
should follow from `h.elim` (one of `h1`, `h2` is `False` from
ValVis on different constructors), but Lean's pattern-match
elaborator doesn't auto-discharge the way `_extends`-style
proofs (which only have 8² combinations) do. A clean approach
likely needs either:
- a helper lemma `ValVis_aux_constructor_match : ValVis_aux n v_a
  v_b h_a h_b → constructor_of v_a = constructor_of v_b` that
  factorizes the mismatch reasoning, *or*
- a tactic-mode proof with carefully-designed `simp_all` automation
  that simplifies each of the 512 sub-goals uniformly.

Estimated: ~150–250 LOC for `ValVis_aux_trans` once the right
proof shape is found. Real proof work, not just plumbing.

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

### ✅ DONE — Closing `frame.eval`'s `.set` case via `HeapEvolution`

`Bisim.lean`'s `.set` framing case is closed (`Bisim.lean` has
zero sorries). The architecture that landed differs from the
sketch in earlier drafts of this document:

**Cross-side `HeapEvolution s_a s_b s_a' s_b'`** (not the same-
side `HeapEvolves` originally proposed):

```
structure HeapEvolution (s_a s_b s_a' s_b' : RunState) : Prop where
  len_a : s_a.heap.length ≤ s_a'.heap.length
  len_b : s_b.heap.length ≤ s_b'.heap.length
  env_preserve : ∀ n env_a env_b, env_a = env_b → ... →
    EnvVis_aux n env_a env_b s_a.heap s_b.heap →
    EnvVis_aux n env_a env_b s_a'.heap s_b'.heap
  val_preserve : ∀ n v_a v_b, ... →
    ValVis_aux n v_a v_b s_a.heap s_b.heap →
    ValVis_aux n v_a v_b s_a'.heap s_b'.heap
```

The same-side `HeapEvolves` originally proposed turned out to be
fundamentally broken for `multnExactPolicy`: it admits
`.builtinBaseApply → multn-closure`, which are different `Val`
constructors and so not same-side bisim-related. The cross-side
formulation works because both sides update with bisim-*related*
new values; same-side old/new aren't required to relate.

**`PolicyRespectsBisim` invariant on `WFCtx.policy_resp`**: the
policy gives the same admit/reject decision on bisim-related
inputs. This lets the `.set` case argue both sides decide the
same way.

**`env_eq` and `heap_len_eq` invariants on `WFCtx`**: ensure
`env.lookup x` produces the same `idx` cross-side, so
`isMetaMutation` agrees and the heap update targets the same
cell on both sides. The `heap_len_eq` invariant maintained
through `.letE` (cons-extension with matching alloc indices).

**Strengthened `ValVis_aux` on closures**: `cenv_a = cenv_b`
structurally. Ensures closure cenvs satisfy `env_eq` recursively.

**`ValVis_aux_update` / `EnvVis_aux_update`** mutual depth
induction with strict `< n` bound on the new-values precondition.
The strict bound is the key trick: it enables a self-update
universal-depth lemma via depth-induction with a strengthened
IH (`∀ k ≤ K, ValVis_aux k`), avoiding the circularity that a
`∀ k` precondition would otherwise create.

Total cost: ~700 LOC of new proved infrastructure. ~30 sites in
`frame`'s proof updated to the new postcondition.

### Outstanding `sorry` in `Policies.lean`

`multnExact_CE_nonnum_case`'s historical proof technique uses an
asymmetric `(s, s_alloc)` framing setup (side A at state `s`,
side B at state `s_alloc` = `s` with the multn closure body's
pre-allocated arg cells). The new `WFCtx.heap_len_eq` invariant
fails for this asymmetric setup, leaving a `sorry` for the
`heap_len_eq` field.

**Resolution path** (~200-300 LOC): a single-side `applyDirect`
prefix-extension lemma:

```
applyDirect at heap h gives (r, s') →
∀ extras, applyDirect at (h ++ extras) gives (r', s'') with
  ValVis r r' s'.heap s''.heap ∧ ...
```

Provable by induction on fuel + cases on `op`, mirroring the
existing framing theorem's `applyDirect` case but for the single-
side prefix-extension setting (envs are the same on both sides;
heaps differ by a prefix-relation). Use this lemma to relate side
A's actual run at `s` to a hypothetical run at `s_alloc`, then
frame symmetrically on `(s_alloc, s_alloc)` where `heap_len_eq`
holds trivially.

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

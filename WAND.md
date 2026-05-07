# WAND.md — defeating the trivialization result

A planning document for a result lean-green is positioned to deliver.
The value-level existential lives in `LeanBlack/Wand.lean`; the
contextual form, W2, and W3 remain. The framing infrastructure
needed to lift to the contextual form is in place — `Bisim.lean`
proves `frame` for all of `eval`, `evalList`, `applyVia`,
`applyDirect`, including the `.set` case.

## The negative result we are defeating

Wand 1998, *The Theory of Fexprs is Trivial*. In an applied λ-calculus
with first-class meta-level access (fexprs / unrestricted reflection),
observational equivalence collapses to α-equivalence:

```
M ≃_obs N   ⟺   M ≡_α N
```

The collapse is one-directional only as a *theorem*: ⟸ is trivial,
⟹ is the content. Given any non-α-equivalent pair, a fexpr context
can crack their syntax open and observe the difference. So the
equational theory you would want — βη, observational congruence over
λ — is gone.

This is the result that justified the field's retreat from reflection.
The keynote framing is that the retreat was premature: the fexpr
collapse depended on the reflective operation acting *unconditionally*.
Once a gate stands between proposal and installation, the collapse
no longer follows.

## Why lean-green can state the positive result

lean-green has the three ingredients required:

1. **Real reflective `set!` against the heap cell holding `base-apply`.**
   Not modeled by an indexed table. `Black.lean`'s `.set` clause
   freezes the active policy `gate := s.policy`, evaluates the RHS,
   then checks `gate ctx oldVal v` against the active gate. The
   meta-level is data; mutation propagates causally.

2. **A parametric policy interface.** `BlackPolicy : MutationCtx →
   Val → Val → Bool` is the gate. Soundness is parameterized over
   an architectural floor `P : Val → Val → Prop`. The canonical
   instances are `CE` (strong) and `CE_weak` (behavioral); see below.
   Each entry of the verified policy table comes with a soundness
   theorem against `P`.

3. **A two-tier value-bisimulation infrastructure.** `Bisim.lean`
   defines `ValVis` (closure-environment-pointwise refinement, à la
   CakeML; structural Lean-equality on captured envs) and the
   framing theorem `frame` for `eval` / `evalList` / `applyVia` /
   `applyDirect`, including the closed `.set` case. It also defines
   `ValVis_weak` — same shape but with the structural-cenv-equality
   clause dropped on the closure case, replaced by pointwise-bisim
   on the cenvs. The bridge `ValVis ⟹ ValVis_weak` is direct.
   `ValVis` is the relation `frame` produces and the `.set` proof
   relies on; `ValVis_weak` is the relation that survives the
   prefix-extension that fresh allocations introduce, and is the
   right behavioral relation for stating CE on higher-order ops.

The headline theorem `multnExact_soundForCE_first_install` is the
concrete instance: under `multnExactPolicy`, post-install behavior
is `ValVis_weak`-related to pre-install behavior on the relevant
trace. (The strong `ValVis` form is unprovable for closure-
returning ops because of the cenv-shift inherent to fresh
allocation; the weak form is the right behavioral statement.)
What WAND.md asks is: *what is the general statement this is an
instance of, and what does it say about the equational theory?*

## Statements, weakest to strongest

The three statements below are stated against `BlackPolicy.SoundForCE_weak`
(the behavioral CE soundness predicate, defined in `Policies.lean`
alongside the strong `SoundForCE`). For first-order ops the two are
equivalent; for closure-returning ops only `SoundForCE_weak` is provable
in general, and it's the right relation for the keynote message ("the
modification didn't break β" is a behavioral claim, not a
syntactic-identity claim).

### W1 — Existential defeat (the minimum claim)

Under any `SoundForCE_weak` policy, observational equivalence is
strictly finer than α-equivalence:

```
theorem wand_defeated_existential
    (policy : BlackPolicy)
    (sound  : policy.SoundForCE_weak) :
  ∃ M N : Expr, ¬ AlphaEquiv M N ∧ ObsEquiv_under policy M N
```

This is the bare minimum statement that the LICS audience needs to
hear. It says: there exist two non-α-equivalent terms that no
context can distinguish under the gated semantics. Witness: any
β-redex and its contractum, e.g. `((λ x. x) 0)` and `0`. Under a
CE_weak-sound policy, no admitted modification can break β at the
apply cell, so no context can distinguish them.

### W2 — βη is contained in observational equivalence

Strengthen the existential to a containment over the standard
λ-calculus equational theory:

```
theorem wand_defeated_strong
    (policy : BlackPolicy)
    (sound  : policy.SoundForCE_weak)
    {M N   : Expr}
    (h     : BetaEtaEquiv M N) :
  ObsEquiv_under policy M N
```

This says: under CE_weak-sound policies, the full βη theory is
observationally valid. The proof goes through the framing theorem:
β-equivalent terms produce `ValVis_weak`-related values across pre-/
post-install heaps, and `ValVis_weak` does not distinguish
β-equivalent operands from observation.

### W3 — Lattice of equational theories

The right structural statement. The map sending a policy to its
induced observational equivalence is monotone (in the right
direction):

```
theorem policy_lattice_monotone
    {P₁ P₂ : BlackPolicy}
    (h : ∀ ctx old new, P₁ ctx old new → P₂ ctx old new) :
  ∀ M N, ObsEquiv_under P₂ M N → ObsEquiv_under P₁ M N
```

A weaker policy (admits less) gives a finer observational
equivalence (more equations hold). The two extremes are:

- `rejectAll` (admits nothing) — observational equivalence under
  this policy contains βη in full. Closest to the standard
  λ-calculus theory.
- `acceptAll` (admits everything) — Wand's collapse: ≃_obs reduces
  to α-equivalence.

Every CE_weak-sound policy sits below `acceptAll` and above (or
equal to) `rejectAll` in this lattice. The non-trivial theories
live in the interior.

This is the keynote-grade statement: *a lattice of equational
theories indexed by the gate, with Wand at the top and βη at the
bottom*.

## Proof strategy

### W1 — concrete witness

The simplest line: pick `M = ((λx. x) 0)` and `N = 0`. Then:

- `¬ AlphaEquiv M N` is immediate (different shapes).
- For `ObsEquiv_under policy M N`: any context `C[·]` either
  - never invokes a gated `.set` — then `C[M]` and `C[N]` evaluate
    identically by ordinary β; or
  - invokes `.set` with some `(old, new)` — then `policy ctx old
    new = true` is required for the install to take effect, and
    `policy.SoundForCE_weak` gives that the post-install dispatch
    is `ValVis_weak`-related to the pre-install dispatch.
    β-reduction commutes with `ValVis_weak`-related dispatch on
    the relevant trace.

Both cases use `frame.eval` (the closed `.set` case included),
together with `applyDirect_heap_extend_weak` (the prefix-extension
lemma in `Bisim.lean`, fully proved via the shift path — see "Why
the headline CE statement is `_weak`" below).

### W2 — induction on βη derivation

Standard: induct on the βη derivation, dispatch each rule to a
`ValVis_weak`-preservation lemma. The hard rule is η at higher type;
under closure-based `ValVis_weak`, η on closures requires showing
that the eta-expanded closure is `ValVis_weak`-related to the
original. The weak relation's closure case demands only
`EnvVis_aux_weak` on cenvs (not Lean equality), which is the right
strength for η at higher type.

Side conditions: closedness of the terms in question (lean-green's
`closedValB` predicate already gates `.quote`); fuel; heap
validity. All of these are already maintained by the runner.

### W3 — lattice monotonicity

By contrapositive on observation: if a context distinguishes `M`
from `N` under `P₂`, every `.set` in the distinguishing trace was
admitted by `P₂`, hence admitted by `P₁` (since `P₁ ⊑ P₂`), hence
the same trace is realized in the `P₁` system, hence the
distinction transfers. Direct.

The interesting half — that `P₁ ⊏ P₂` strictly induces `≃_{P₂}
⊏ ≃_{P₁}` — requires constructing distinguishing pairs, which
goes via Wand-style adversarial contexts that the larger policy
admits. Not free.

## Concrete proof obligations

In rough order of dependency:

1. **Define `ObsEquiv_under : BlackPolicy → Expr → Expr → Prop`.**
   Standard contextual equivalence over lean-green's `Expr`,
   parameterized over the active policy. Requires settling on a
   notion of "context" — the natural one is `Expr` with a hole,
   evaluated with the given policy as the runner's active gate.

2. **Lift `LeanBlack/Wand.lean`'s value-level existential to the
   full contextual `wand_defeated_existential` (W1).** The framing
   theorem `frame` discharges the inductive cases; the witness is
   the β-redex `((λx.x) 0)` and its contractum `0`. Requires (1).

3. **Define `BetaEtaEquiv` over `Expr`.** Probably already
   derivable from `Black.lean`'s evaluation relation; if not, a
   small development.

4. **Prove `wand_defeated_strong` (W2)** by induction on
   `BetaEtaEquiv`. Each rule reduces to a `ValVis`-preservation
   step. Bigger development; depends on (1)–(3).

5. **Prove `policy_lattice_monotone` (W3)** by trace replay.
   Requires (1).

6. **Optional: name the extremes.** Prove `≃_{rejectAll}` extends
   βη and `≃_{acceptAll} = α-equivalence` (the latter is just
   Wand's theorem reproduced in lean-green's setting, a sanity
   check that the framework recovers the negative result when the
   gate is trivial).

## What this buys the keynote

W1 alone is enough for the talk: it is the precise positive
counterpart of Wand. State it on the slide, prove it on the
spot at β-redex granularity, declare victory. The audience
remembers the trivialization result; the result they didn't have
is that gating recovers a non-trivial theory.

W3 is the structural punchline that turns "we have an artifact"
into "we have a theorem the LICS community can develop." A
lattice of equational theories indexed by admission policies is
the kind of object the LICS community knows how to study.

W2 is the bridge — the practical claim that the standard
equational theory of λ is *available* under any reasonable gate,
not just a curiosity at the bottom of a lattice.

## Relation to the rest of the development

- `multnExact_soundForCE_first_install` is the operational
  archetype of W1: a single concrete CE_weak-sound policy, a
  single concrete admitted install, and `ValVis_weak` between
  pre and post. W1 is the universal-quantifier closure of that
  pattern.
- `BlackPolicy.SoundForCE_weak` is exactly the hypothesis the
  WAND theorems take. It is already the soundness predicate the
  architecture uses post the two-tier refactor. No new predicate
  needs to be invented.
- `Bisim.lean` is the proof infrastructure. The two-tier `ValVis`
  / `ValVis_weak` development is in place; the `.set` framing
  case is closed; `applyDirect_heap_extend_weak` is fully proved
  (via the functional shift path).

This is why WAND.md is a *future* document, not a separate
project: the artifact is most of the way there structurally.
What is missing is (a) defining contextual equivalence, (b)
writing the theorems.

## Why the headline CE statement is `_weak`

The `.set` framing case is closed. Closing it required strengthening
`ValVis_aux_closure` to demand Lean-equal cenvs on related closures
(combined with `WFCtx.env_eq`, this forces cross-side cell updates
to target the same heap index). That strengthening is load-bearing:
it's what makes the `.set` proof go through.

The closing of CE for the multn-style install runs into a
consequence of that strengthening. The proof technique runs side A
at `s` and side B at `s_alloc = s.heap ++ [op, listToVal operands]`
(the multn closure body's pre-allocated arg cells). Fresh
allocations on side B happen at indices shifted by two from their
side-A counterparts. Any `.lam` evaluated under the resulting env
produces a closure whose cenv is the current env — which is *not*
Lean-equal across the two sides on the args-binding portion. So
`ValVis_aux_closure` fails on the result, and the strong `CE`
claim is **false** for closure-returning ops.

**The fix is two-tier bisim.** `ValVis_weak` drops the Lean-
equality requirement, keeping only the pointwise-bisim relation on
cenvs. Under `ValVis_weak`, the cenvs look up to bisim cells (the
args have the same values, just at different addresses), so the
relation holds for higher-order results. `CE_weak` is the
behavioral CE statement that's true and what the keynote should
claim.

The two-tier architecture is additive: `ValVis ⟹ ValVis_weak` via
the bridge `ValVis_to_weak`. Existing strong-`ValVis` proofs (the
`.set` framing, `frame`, the policy-soundness theorems on inputs)
are unchanged. CE on outputs is downgraded to the weak form, which
is what behavioral equivalence requires anyway.

**`applyDirect_heap_extend_weak` is closed** via the functional
shift path. The cenv-shift obstruction (which made the strong
`ValVis` formulation false for closure-returning ops) is resolved
by viewing prefix-extension as a syntactic operation: `shift_idx`
on heap indices, lifted compositionally through `shift_val` /
`shift_env` / `shift_heap`. The joint shift-commutativity theorem
`shift_respect` (eval / evalList / applyVia / applyDirect all
commute with shift) gives the prefix-extension lemma directly,
with the result-side bridge to `ValVis_weak r r'` provided by
`valVis_self_shift` (a value is weakly bisim with its own shift).
The `.set` case threads `PolicyRespectsShift` (the shift-flavored
analog of `PolicyRespectsBisim`); `verifiedTable_respects_shift`
discharges this for the verified policies.

## References

- M. Wand. *The Theory of Fexprs is Trivial*. Lisp and Symbolic
  Computation, 1998.
- Pre-Wand fexpr work for context: M. Felleisen 1991 on
  expressiveness; J. Pitman on MacLisp fexprs.
- Asai, Matsuoka, Yonezawa 1996, *Compiling and Optimizing with
  Continuations* / Black implementation, for the reflective
  substrate this development verifies a core of.
- Kumar 2016, *Self-Compilation and Self-Verification* (CakeML
  thesis), Chapter 3, for the data-refinement-based bisimulation
  style `ValVis` instantiates.

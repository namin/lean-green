# WAND.md — defeating the trivialization result

A planning document for a result that lean-green is in position to
state and (eventually) prove. Not yet started in the artifact; this
file records the target so it isn't lost.

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
   instance is `ConservativeExt`. Each entry of the verified policy
   table comes (or should come) with a soundness theorem against `P`.

3. **A value-bisimulation infrastructure.** `Bisim.lean` defines
   `ValVis` (closure-environment-pointwise refinement, à la CakeML)
   and the framing theorem `frame` for `eval` / `evalList` /
   `applyVia` / `applyDirect`. This is the machinery that lets us
   reason about post-mutation behavior up to data refinement rather
   than syntactic identity.

The headline theorem `multnExact_soundForCE_first_install` is the
concrete instance: under `multnExactPolicy`, post-install behavior
is `ValVis`-related to pre-install behavior on the relevant trace.
What WAND.md asks is: *what is the general statement this is an
instance of, and what does it say about the equational theory?*

## Statements, weakest to strongest

### W1 — Existential defeat (the minimum claim)

Under any `ConservativeExt`-sound policy, observational equivalence
is strictly finer than α-equivalence:

```
theorem wand_defeated_existential
    (policy : BlackPolicy)
    (sound  : Policy.UnivSoundFor ConservativeExt policy) :
  ∃ M N : Expr, ¬ AlphaEquiv M N ∧ ObsEquiv_under policy M N
```

This is the bare minimum statement that the LICS audience needs to
hear. It says: there exist two non-α-equivalent terms that no
context can distinguish under the gated semantics. Witness: any
β-redex and its contractum, e.g. `((λ x. x) 0)` and `0`. Under a
CE-sound policy, no admitted modification can break β at the apply
cell, so no context can distinguish them.

### W2 — βη is contained in observational equivalence

Strengthen the existential to a containment over the standard
λ-calculus equational theory:

```
theorem wand_defeated_strong
    (policy : BlackPolicy)
    (sound  : Policy.UnivSoundFor ConservativeExt policy)
    {M N   : Expr}
    (h     : BetaEtaEquiv M N) :
  ObsEquiv_under policy M N
```

This says: under CE-sound policies, the full βη theory is
observationally valid. The proof goes through the framing theorem:
β-equivalent terms produce `ValVis`-related values across pre-/post-
install heaps, and `ValVis` does not distinguish β-equivalent
operands from observation.

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

Every CE-sound policy sits below `acceptAll` and above (or equal
to) `rejectAll` in this lattice. The non-trivial theories live
in the interior.

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
    `Policy.UnivSoundFor ConservativeExt policy` gives that the
    post-install dispatch is CE-related to the pre-install
    dispatch. β-reduction commutes with CE-related dispatch on the
    relevant trace.

The second case is where most of the work lives. The framing
theorem `frame.eval` (lean-green's existing development) is
exactly what discharges it — except for the open `.set` case
(currently `sorry`). Closing that case is the prerequisite. See
`README.md` *Open work* and `FUTURE.md` *Generalizing the
infrastructure* for the three architectural options.

### W2 — induction on βη derivation

Standard: induct on the βη derivation, dispatch each rule to a
`ValVis`-preservation lemma. The hard rule is η at higher type;
under closure-based `ValVis`, η on closures requires showing that
the eta-expanded closure is `ValVis`-related to the original,
which is true if `ValVis` respects the operational reading of the
body. For the lean-green `Val` type this is direct.

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

2. **Close the `.set` case of `frame.eval`.** The W1/W2 proofs
   route through `frame`. The current `sorry` is the gap. Three
   architectural options in `FUTURE.md`:
   - restrict `frame`'s domain to set-free expressions;
   - replace `HeapExt` with a `HeapEvolves` relation respecting
     a policy-bisim invariant (~500 LOC);
   - replace `ValVis` with a step-indexed logical relation (major
     rewrite).

3. **Prove `wand_defeated_existential` (W1)** with the β-redex
   witness. Requires (1) and (2). Small additional development on
   top.

4. **Define `BetaEtaEquiv` over `Expr`.** Probably already
   derivable from `Black.lean`'s evaluation relation; if not, a
   small development.

5. **Prove `wand_defeated_strong` (W2)** by induction on `BetaEtaEquiv`.
   Each rule reduces to a `ValVis`-preservation step. Bigger
   development; depends on (1)–(4).

6. **Prove `policy_lattice_monotone` (W3)** by trace replay.
   Requires (1). Independent of (2) modulo the framing-theorem
   gap that already affects W1.

7. **Optional: name the extremes.** Prove `≃_{rejectAll}` extends
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
  archetype of W1: a single concrete CE-sound policy, a single
  concrete admitted install, and `ValVis` between pre and post.
  W1 is the universal-quantifier closure of that pattern.
- `Policy.UnivSoundFor ConservativeExt` is exactly the hypothesis
  the WAND theorems take. It is already the soundness predicate
  the architecture uses. No new predicate needs to be invented.
- `Bisim.lean` is the proof infrastructure. Nothing new is
  required at the bisimulation layer beyond closing the open
  `.set` case.

This is why WAND.md is a *future* document, not a separate
project: the artifact is already most of the way there
structurally. What is missing is (a) closing the framing gap,
(b) defining contextual equivalence, (c) writing the theorems.

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

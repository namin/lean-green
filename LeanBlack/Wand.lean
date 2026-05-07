/-
  LeanBlack/Wand.lean — toward the WAND-defeated theorems.

  Wand 1998 (`The Theory of Fexprs is Trivial`) proved that under
  unconstrained first-class meta-level access, observational
  equivalence collapses to α-equivalence. With a gate, the collapse
  no longer follows: the equational theory under the gated
  evaluator can be richer than α-equivalence.

  This file lands the **value-level existential defeat**: there
  exist non-syntactically-equal expressions whose top-level
  evaluation under any policy table agrees, and which agree in
  several concrete contexts as well. The witness is a β-redex /
  contractum pair: `((λx.x) 0)` and `0`. They evaluate to `.num 0`
  regardless of the active `PolicyTable` because neither contains
  `.set` or `.installPolicy`.

  The **full contextual existential** promised by `WAND.md` (W1) —
  the universal quantifier over arbitrary syntactic contexts,
  including those that install gated `.set` modifications — is the
  next step. It requires a syntactic-context notion (`Expr` with a
  hole + a `fillHole` operation) and an inductive lift via the
  `frame` theorem in `Bisim.lean`. See `WAND.md` for the full
  proof obligation list.

  W2 (`βη ⊆ ≃_obs`) and W3 (the lattice of equational theories
  indexed by policies) are further out.
-/

import LeanBlack.Black

namespace LeanBlack.Wand

open LeanBlack

/-- The β-redex `((λx.x) 0)`. -/
def betaRedex : Expr :=
  .app [.lam ["x"] (.var "x"), .num 0]

/-- The β-contractum `0`. -/
def betaContractum : Expr :=
  .num 0

/-- The redex is not syntactically equal to the contractum. -/
theorem betaRedex_ne_contractum : betaRedex ≠ betaContractum := by
  intro h
  injection h

/-- Top-level value-level existential defeat: there exist
    non-syntactically-equal expressions whose top-level evaluation
    agrees under any policy table.

    Wand's collapse said observational equivalence reduces to
    α-equivalence under unconstrained reflection. The witness here
    is two non-α-equivalent expressions whose top-level evaluation
    produces the same value, regardless of the active policy
    table — a non-trivial existential equivalence beyond α. -/
theorem wand_defeated_top_level :
    ∃ M N : Expr, M ≠ N ∧
      ∀ (ptable : PolicyTable),
        evalProgram 10 ptable M = evalProgram 10 ptable N := by
  refine ⟨betaRedex, betaContractum, betaRedex_ne_contractum, ?_⟩
  intro _
  rfl

/-- The redex and contractum agree inside a `letE` context that
    binds them to a name and reads the binding back: even though
    the redex performs an extra heap allocation during its
    evaluation, the let-bound result agrees with the
    contractum's. -/
theorem wand_defeated_letE_var :
    ∀ (ptable : PolicyTable),
      evalProgram 20 ptable (.letE "y" betaRedex (.var "y")) =
      evalProgram 20 ptable (.letE "y" betaContractum (.var "y")) := by
  intro _
  rfl

/-- The redex and contractum agree inside a `letE` context whose
    body is a constant — the let binding does not project the
    redex's value but the surrounding evaluation still proceeds
    identically. -/
theorem wand_defeated_letE_const :
    ∀ (ptable : PolicyTable),
      evalProgram 20 ptable (.letE "y" betaRedex (.num 42)) =
      evalProgram 20 ptable (.letE "y" betaContractum (.num 42)) := by
  intro _
  rfl

/-- The redex and contractum agree as the final step of a
    sequence whose prelude does some unrelated work. The prelude
    runs identically on both sides; the redex / contractum
    produce the same value. -/
theorem wand_defeated_seq :
    ∀ (ptable : PolicyTable),
      evalProgram 20 ptable
        (.seq [.num 7, .num 8, betaRedex]) =
      evalProgram 20 ptable
        (.seq [.num 7, .num 8, betaContractum]) := by
  intro _
  rfl

end LeanBlack.Wand

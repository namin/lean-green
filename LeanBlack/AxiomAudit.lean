import LeanBlack.Policies
import LeanBlack.Wand

/-!
# Axiom audit

Machine-witnesses that lean-green's headline results rest only on the Lean kernel
plus the standard classical axioms — crucially, **no `Lean.ofReduceBool`** (the
axiom `native_decide` injects to trust the compiler instead of the kernel) and no
`sorryAx`. Each `#guard_msgs in #print axioms …` pins the exact footprint, so the
build fails the moment any audited theorem acquires a new axiom.
-/

/-- info: 'multnExact_soundForCE_first_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multnExact_soundForCE_first_install

/-- info: 'verifiedTable_respects_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verifiedTable_respects_shift

/-- info: 'acceptAllPolicy_respects_shift' does not depend on any axioms -/
#guard_msgs in
#print axioms acceptAllPolicy_respects_shift

/-- info: 'LeanBlack.Wand.wand_defeated_top_level' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanBlack.Wand.wand_defeated_top_level

/-- info: 'LeanBlack.Wand.wand_defeated_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanBlack.Wand.wand_defeated_seq

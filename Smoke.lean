/-
  Smoke tests for lean-black.

  Three scenes:

  1. *Un-governed* (default `acceptAllPolicy`): the multn-via-`set!`
     pattern works, but so does a *malicious* modification that
     overwrites `base-apply` with a constant-returning closure —
     after which `(+ 1 2)` evaluates to `0`. This is the
     reflection-without-governance failure mode.

  2. *Loose-governed* (after `(installPolicy idx_numGuard)`): the
     constant-returning bad mod is refused (the new value doesn't
     match the recognized shape); the multn modification is admitted;
     base-level arithmetic is preserved. But `numGuardPolicy` is
     loose — its else-branch is unconstrained — so adversarial
     `numGuard`-shaped modifications can still break CE on
     non-numeric operators.

  3. *Strict-governed + adversarial* (after `(installPolicy
     idx_multnExact)`): `multnExactPolicy` checks the strict multn
     shape *and* the install-protocol facts (`OrigBoundIn`,
     `NumQBoundIn`) at runtime via `MutationCtx`. This refuses the
     `numGuard`-shaped malicious wrapper and the shadowed-`orig`
     attack that would have slipped through a runtime gate that
     only checked syntactic shape. It also refuses a TOCTOU
     `installPolicy`-mid-RHS downgrade (the policy is now frozen
     before the RHS evaluates).

  The same mutation mechanism — `set!` against the meta-env's
  `base-apply` cell from inside `(em ...)` — is gated by whichever
  policy is active. Switching policies via `installPolicy` is itself
  an explicit reflective step.
-/

import LeanBlack.Black
import LeanBlack.Policies

def fuel : Nat := 10000

/-! ## Programs -/

/-- The multn wrapper: matches `numGuardPolicy`'s recognized shape
    *and* `multnExactPolicy`'s strict shape. -/
def multnWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      (.primApp (.var "orig") [.var "op", .var "args"])

/-- Install multn:
    `(em (let ((orig base-apply)) (set! base-apply <wrapper>)))`. -/
def installMultn : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" multnWrapper

/-- A malicious modification: a binary closure that ignores its
    arguments and returns `0`. Under `acceptAllPolicy` this admits;
    after install, every base-level application returns `0`. Under
    `numGuardPolicy` this is refused — the body is not an `ifte`
    on `num?`. -/
def badModWrapper : Expr :=
  .lam ["op", "args"] (.num 0)

def installBadMod : Expr :=
  .em <| .set "base-apply" badModWrapper

/-! ## Scene 1: un-governed run -/

def test_plus : Option Val :=
  evalProgram fuel [] (.app [.var "+", .num 1, .num 2])

def test_no_multn : Option Val :=
  evalProgram fuel [] (.app [.num 2, .num 3, .num 4])

def test_multn : Option Val :=
  evalProgram fuel [] <| .seq [installMultn, .app [.num 2, .num 3, .num 4]]

def test_multn_preserves_plus : Option Val :=
  evalProgram fuel [] <| .seq [installMultn, .app [.var "+", .num 1, .num 2]]

def test_badmod_breaks_plus : Option Val :=
  evalProgram fuel [] <| .seq [installBadMod, .app [.var "+", .num 1, .num 2]]

/-! ## Scene 2: governed run (numGuardPolicy active) -/

/-- Install `numGuardPolicy` first, then attempt the bad mod (refused),
    then `(+ 1 2)` (still works). -/
def test_governed_refuses_badmod : Option (Val × Val) :=
  let prog : Expr :=
    .seq [
      .installPolicy Policy.idx_numGuard,
      .letE "rejectVerdict" installBadMod <|
        .letE "plusResult" (.app [.var "+", .num 1, .num 2]) <|
          .app [.var "cons", .var "rejectVerdict",
            .app [.var "cons", .var "plusResult", .quote .nilV]]
    ]
  match evalProgram fuel verifiedTable prog with
  | some (.cons verdict (.cons result .nilV)) => some (verdict, result)
  | _ => none

def test_governed_admits_multn : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_numGuard,
      installMultn,
      .app [.num 2, .num 3, .num 4]
    ]

/-! ## Scene 3: strict-governed + adversarial (multnExactPolicy active)

    These tests demonstrate `multnExactPolicy`'s runtime
    install-protocol checks. The policy now sees a `MutationCtx`
    (target name, heap, captured-env contents) and refuses
    proposals that match the multn shape but violate
    `OrigBoundIn` / `NumQBoundIn` or target a non-`base-apply`
    binding. -/

/-- Adversarial #1 — `numGuard`-shaped malicious wrapper. Body has
    the `(if (num? op) ... ...)` shape that `numGuardPolicy`
    accepts, but the else-branch is `0` (not a delegating
    `(orig op args)`). Passes `numGuardPolicy`; refused by
    `multnExactPolicy` because the strict shape requires the
    delegating else-branch. -/
def numGuardMaliciousWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.num 24)            -- pretends to multiply for numerics
      (.num 0)             -- breaks CE on non-numerics

def installNumGuardMalicious : Expr :=
  .em <| .set "base-apply" numGuardMaliciousWrapper

/-- Adversarial #2 — shadowed-`orig`. The proposal looks like the
    canonical multn install — outer `let orig base-apply` then
    `set! base-apply <multn>` — but a *second* `let orig` shadows
    `orig` with a literal `.num 0` before the `.lam`. The closure
    captures the shadowed binding; its `(orig op args)` resolves
    to applying `.num 0` to `[op, args]`. `multnExactPolicy`
    refuses by checking `OrigBoundIn` against `ctx.heap`: the
    shadowed cell holds `.num 0`, not `.builtinBaseApply`. -/
def shadowedOrigInstall : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|        -- correct outer let
      .letE "orig" (.num 0) <|                  -- shadowed!
        .set "base-apply" multnWrapper

/-- Adversarial #3 — TOCTOU `installPolicy`-mid-RHS downgrade. The
    proposal first tries `installPolicy idx_rejectAll` mid-RHS
    (which would lock down all future mutations), then returns the
    canonical multn body. With the gate frozen at the start of
    `.set` (item 1 of FUTURE.md / Hardening seam), the
    pre-downgrade gate decides — and `multnExactPolicy` admits the
    multn shape under its own checks. The `installPolicy` call
    *does* take effect post-`.set`, but doesn't authorize the
    `.set` itself.

    The point of this test isn't to break the install — it's to
    show the install proceeds *under the gate that was active at
    the moment .set started*, regardless of what the RHS does to
    `s.policy` along the way. -/
def installMultnWithMidRHSDowngrade : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" <|
        .seq [
          .installPolicy Policy.idx_rejectAll,   -- TOCTOU attempt
          multnWrapper                            -- canonical multn body
        ]

/-- Adversarial #4 — non-`base-apply` target. Try to install a
    multn-shaped closure into the `+` cell of metaEnv. `target =
    "+" ≠ "base-apply"`, so `multnExactPolicy` refuses regardless
    of shape. -/
def installMultnAtPlus : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "+" multnWrapper

/-- Adversarial #5 — multi-install. The runtime gate is now
    `oldVal`-parametric: the captured `orig` cell must hold
    *whatever value is currently at `base-apply`*, not specifically
    `.builtinBaseApply`. So a *second* install — where the captured
    `orig` is the first install's multn closure — should admit too.

    First install: M₁ with orig = .builtinBaseApply. Admitted (canonical).
    Second install: M₂ with orig = M₁ (the let snapshots the
    current base-apply, which is M₁). `multnExactPolicy` checks
    `Val.beq <heap[idx_o]> <oldVal=M₁>` and admits.

    Witness: after the chain, `(2 3 4) ⇒ 24` — multn behavior
    survives. (Both installs use `multnWrapper`, so the chain
    is functionally idempotent.) -/
def test_strict_multi_install : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_multnExact,
      installMultn,                                  -- install M₁
      installMultn,                                  -- install M₂; orig = M₁
      .app [.num 2, .num 3, .num 4]                  -- still 24
    ]

/-- Witness: under `multnExactPolicy`, the canonical multn install
    is admitted and `(2 3 4) ⇒ 24`. -/
def test_strict_admits_multn : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_multnExact,
      installMultn,
      .app [.num 2, .num 3, .num 4]
    ]

/-- Witness: `(+ 1 2) = 3` is preserved under multn install. -/
def test_strict_multn_preserves_plus : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_multnExact,
      installMultn,
      .app [.var "+", .num 1, .num 2]
    ]

/-- Adversarial #1 result. Returns `(verdict, plus_result)` — the
    `set!` returns `verdict = false` (refused), `(+ 1 2)` returns
    `3` (the malicious mod was *not* installed). -/
def test_strict_refuses_numguard_malicious : Option (Val × Val) :=
  let prog : Expr :=
    .seq [
      .installPolicy Policy.idx_multnExact,
      .letE "verdict" installNumGuardMalicious <|
        .letE "plusResult" (.app [.var "+", .num 1, .num 2]) <|
          .app [.var "cons", .var "verdict",
            .app [.var "cons", .var "plusResult", .quote .nilV]]
    ]
  match evalProgram fuel verifiedTable prog with
  | some (.cons verdict (.cons result .nilV)) => some (verdict, result)
  | _ => none

/-- Adversarial #2 result: shadowed-`orig` is refused. -/
def test_strict_refuses_shadowed_orig : Option (Val × Val) :=
  let prog : Expr :=
    .seq [
      .installPolicy Policy.idx_multnExact,
      .letE "verdict" shadowedOrigInstall <|
        .letE "plusResult" (.app [.var "+", .num 1, .num 2]) <|
          .app [.var "cons", .var "verdict",
            .app [.var "cons", .var "plusResult", .quote .nilV]]
    ]
  match evalProgram fuel verifiedTable prog with
  | some (.cons verdict (.cons result .nilV)) => some (verdict, result)
  | _ => none

/-- Adversarial #3 result: with the gate frozen, the multn install
    succeeds *under the multnExact gate that was active when .set
    started*, even though the RHS attempted a downgrade. The
    install verdict is `true` (admitted). After the install
    completes, `s.policy = rejectAll` (the downgrade *did* take
    effect, but only post-`.set`); subsequent mutations would be
    refused. We check that `(2 3 4) ⇒ 24` still works (multn was
    installed), and that an attempted second `.set! base-apply`
    after the install is refused (since policy is now
    `rejectAll`). -/
def test_strict_freeze_admits_install : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_multnExact,
      installMultnWithMidRHSDowngrade,
      .app [.num 2, .num 3, .num 4]
    ]

def test_strict_freeze_post_install_locked : Option Val :=
  evalProgram fuel verifiedTable <|
    .seq [
      .installPolicy Policy.idx_multnExact,
      installMultnWithMidRHSDowngrade,
      installBadMod   -- should be refused: policy is now rejectAll
    ]

/-- Adversarial #4 result: a multn-shape install targeting `+`
    instead of `base-apply` is refused. -/
def test_strict_refuses_wrong_target : Option (Val × Val) :=
  let prog : Expr :=
    .seq [
      .installPolicy Policy.idx_multnExact,
      .letE "verdict" installMultnAtPlus <|
        .letE "plusResult" (.app [.var "+", .num 1, .num 2]) <|
          .app [.var "cons", .var "verdict",
            .app [.var "cons", .var "plusResult", .quote .nilV]]
    ]
  match evalProgram fuel verifiedTable prog with
  | some (.cons verdict (.cons result .nilV)) => some (verdict, result)
  | _ => none

/-! ## Reporting -/

/-- Mutable failure counter. CI relies on `main` exiting non-zero
    when any test fails, so the suite is genuinely actionable. -/
initialize failureCount : IO.Ref Nat ← IO.mkRef 0

def reportLine (label : String) (actual expected : Option Val) : IO Unit := do
  let actualStr   := toString (repr actual)
  let expectedStr := toString (repr expected)
  let ok := actualStr == expectedStr
  let mark := if ok then "OK  " else "FAIL"
  if ¬ ok then failureCount.modify (· + 1)
  IO.println s!"{mark} {label}: {actualStr}"

def reportPair (label : String) (actual expected : Option (Val × Val)) : IO Unit := do
  let actualStr   := toString (repr actual)
  let expectedStr := toString (repr expected)
  let ok := actualStr == expectedStr
  let mark := if ok then "OK  " else "FAIL"
  if ¬ ok then failureCount.modify (· + 1)
  IO.println s!"{mark} {label}: {actualStr}"

def main : IO Unit := do
  IO.println "-- scene 1: un-governed (default acceptAllPolicy) --"
  reportLine "(+ 1 2)"                  test_plus                  (some (.num 3))
  reportLine "(2 3 4) un-multn'd"       test_no_multn              none
  reportLine "(2 3 4) post-multn"       test_multn                 (some (.num 24))
  reportLine "(+ 1 2) post-multn"       test_multn_preserves_plus  (some (.num 3))
  reportLine "(+ 1 2) post-badmod"      test_badmod_breaks_plus    (some (.num 0))
  IO.println ""
  IO.println "-- scene 2: loose-governed (numGuardPolicy active) --"
  reportPair "constant badmod refused"  test_governed_refuses_badmod
                                        (some (.bool false, .num 3))
  reportLine "(2 3 4) post-multn"       test_governed_admits_multn (some (.num 24))
  IO.println ""
  IO.println "-- scene 3: strict-governed + adversarial (multnExactPolicy active) --"
  reportLine "multn install admitted"   test_strict_admits_multn   (some (.num 24))
  reportLine "(+ 1 2) preserved"        test_strict_multn_preserves_plus
                                        (some (.num 3))
  reportPair "numGuard-shaped malicious refused"
                                        test_strict_refuses_numguard_malicious
                                        (some (.bool false, .num 3))
  reportPair "shadowed-orig refused"    test_strict_refuses_shadowed_orig
                                        (some (.bool false, .num 3))
  reportLine "TOCTOU freeze: install succeeds under frozen gate"
                                        test_strict_freeze_admits_install
                                        (some (.num 24))
  reportLine "TOCTOU freeze: post-install locked by downgrade"
                                        test_strict_freeze_post_install_locked
                                        (some (.bool false))
  reportPair "wrong target (`+` not `base-apply`) refused"
                                        test_strict_refuses_wrong_target
                                        (some (.bool false, .num 3))
  reportLine "multi-install (M₂ ∘ M₁): both admitted, multn preserved"
                                        test_strict_multi_install
                                        (some (.num 24))
  let n ← failureCount.get
  if n > 0 then
    IO.println s!"\n{n} failure(s)."
    IO.Process.exit 1
  IO.println "\nAll tests passed."

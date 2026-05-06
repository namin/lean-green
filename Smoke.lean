/-
  Smoke tests for lean-black.

  Two scenes:

  1. *Un-governed* (default `acceptAllPolicy`): the multn-via-`set!`
     pattern works, but so does a *malicious* modification that
     overwrites `base-apply` with a constant-returning closure —
     after which `(+ 1 2)` evaluates to `0`. This is the
     reflection-without-governance failure mode.

  2. *Governed* (after `(installPolicy idx_numGuard)`): the malicious
     modification is refused (the new value doesn't match the
     recognized shape); the multn modification is admitted; base-level
     arithmetic is preserved.

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

/-! ## Reporting -/

def reportLine (label : String) (actual expected : Option Val) : IO Unit := do
  let actualStr   := toString (repr actual)
  let expectedStr := toString (repr expected)
  let mark := if actualStr == expectedStr then "OK  " else "FAIL"
  IO.println s!"{mark} {label}: {actualStr}"

def reportPair (label : String) (actual expected : Option (Val × Val)) : IO Unit := do
  let actualStr   := toString (repr actual)
  let expectedStr := toString (repr expected)
  let mark := if actualStr == expectedStr then "OK  " else "FAIL"
  IO.println s!"{mark} {label}: {actualStr}"

def main : IO Unit := do
  IO.println "-- scene 1: un-governed (default acceptAllPolicy) --"
  reportLine "(+ 1 2)"                  test_plus                  (some (.num 3))
  reportLine "(2 3 4) un-multn'd"       test_no_multn              none
  reportLine "(2 3 4) post-multn"       test_multn                 (some (.num 24))
  reportLine "(+ 1 2) post-multn"       test_multn_preserves_plus  (some (.num 3))
  reportLine "(+ 1 2) post-badmod"      test_badmod_breaks_plus    (some (.num 0))
  IO.println ""
  IO.println "-- scene 2: governed (numGuardPolicy active) --"
  reportPair "badmod refused, plus ok"  test_governed_refuses_badmod
                                        (some (.bool false, .num 3))
  reportLine "(2 3 4) post-multn"       test_governed_admits_multn (some (.num 24))

/-
  Elaborate an LLM-proposed `set!`-on-`base-apply` modification by
  delegating to Lean itself.

  The LLM proposes an `Expr` term — typically a `.lam ["op", "args"] ...`
  closure — that, when installed via `(em (let ((orig base-apply)) (set! base-apply <PROP>)))`,
  replaces the meta-env's `base-apply`. Whether the install succeeds
  is decided by the **active policy** at install time.

  We write a tiny wrapper file:

      import LeanBlack
      def proposalExpr : Expr := <SPLICED LLM SOURCE>
      def runTest : Expr := .seq [
        .installPolicy 1,                           -- numGuardPolicy
        .letE "verdict"
          (.em (.letE "orig" (.var "base-apply")
            (.set "base-apply" proposalExpr)))
          (.letE "result" (.app [.num 2, .num 3, .num 4])
            (.app [.var "cons", .var "verdict", .var "result"]))
      ]
      def main : IO Unit := ...

  …and run it via `lake env lean --run`. The wrapper prints
  "ADMITTED-RESULT <repr>" if the policy admitted the proposal and
  the test program ran, "REJECTED" if the policy refused, or an
  elaboration error if the proposal didn't compile.

  Single-stage gate (witness via current policy). The proof stage is
  deferred — adding it requires a Lean-level proof obligation
  (e.g. `MultnExactShape` or eventually `CE`), which the LLM would
  supply alongside the modification.
-/

import LeanBlack.Black
import LeanBlack.Policies

namespace LeanBlack.Elab

inductive Result where
  | elabError (msg : String)
  | rejected
  /-- Proposal admitted by the active policy. `witnessResult` is the
      `repr` of the test program's result after install. -/
  | admitted (witnessResult : Option String)
  deriving Repr

def Result.isAdmitted : Result → Bool
  | .admitted _ => true
  | _ => false

instance : ToString Result where
  toString
    | .elabError m         => s!"ELAB-ERROR: {m}"
    | .rejected            => "REJECTED"
    | .admitted none       => "ADMITTED (witness produced none)"
    | .admitted (some r)   => s!"ADMITTED → {r}"

structure Config where
  wrapperPath : String := "/tmp/leanblack-cascade-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`. -/
  workingDir  : Option String := none

def defaultConfig : Config := {}

private def buildWrapper (proposalSrc : String) : String :=
  s!"import LeanBlack

def proposalExpr : Expr :=
{proposalSrc}

def runTest : Expr :=
  .seq [
    .installPolicy 1,
    .letE \"verdict\"
      (.em (.letE \"orig\" (.var \"base-apply\")
        (.set \"base-apply\" proposalExpr)))
      (.letE \"result\" (.app [.num 2, .num 3, .num 4])
        (.app [.var \"cons\", .var \"verdict\", .var \"result\"]))
  ]

def main : IO Unit := do
  match evalProgram 100000 verifiedTable runTest with
  | none => IO.println \"ELAB-EVAL-FAILED\"
  | some (.cons (.bool false) _) => IO.println \"REJECTED\"
  | some (.cons (.bool true) result) => IO.println s!\"ADMITTED-RESULT \{repr result}\"
  | some other => IO.println s!\"UNEXPECTED-RESULT \{repr other}\"
"

private def runWrapper (path : String) (workingDir : Option String) :
    IO (Bool × String × String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", path]
    cwd := workingDir
  }
  return (out.exitCode == 0, out.stdout, out.stderr)

/-- Elaborate the LLM's proposal, run the wrapper, parse the verdict. -/
def checkProposal (cfg : Config) (proposalSrc : String) : IO Result := do
  IO.FS.writeFile cfg.wrapperPath (buildWrapper proposalSrc)
  let (ok, stdout, stderr) ← runWrapper cfg.wrapperPath cfg.workingDir
  if !ok then return .elabError (stdout ++ stderr).trim
  let lastLine := (stdout.trim.splitOn "\n").getLast?.getD ""
  if lastLine == "REJECTED" then return .rejected
  if lastLine.startsWith "ADMITTED-RESULT " then
    return .admitted (some (lastLine.drop "ADMITTED-RESULT ".length))
  if lastLine == "ELAB-EVAL-FAILED" then
    return .elabError "evaluator failed (out of fuel or malformed expression)"
  return .elabError s!"unexpected wrapper output:\n{stdout}"

end LeanBlack.Elab

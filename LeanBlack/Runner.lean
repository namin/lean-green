/-
  An LLM/Lean cascade over the lean-black gate.

  Each round:
    1. Prompt Bedrock for a PROPOSAL (a Lean 4 `Expr` term that, when
       installed via `(em (let ((orig base-apply)) (set! base-apply <PROP>)))`,
       replaces the meta-env's `base-apply`).
    2. Write a wrapper file, run `checkProposal`. The wrapper installs
       under `multnExactPolicy` and runs a fixed witness program
       `(2 3 4)`.
    3. Outcome: `.elabError` (proposal didn't elaborate),
       `.rejected` (policy refused), or `.admitted` (policy admitted,
       witness program ran).
    4. On elab error, retry up to `maxRetries` times with the
       diagnostic fed back into the prompt.

  ## What this enforces

  `multnExactPolicy` is **CE-sound** for the install-protocol
  invariants it checks at runtime via `MutationCtx`:

  - target = "base-apply" (no other meta-env cell may be replaced)
  - structural multn shape (strict: delegating else-branch)
  - `OrigBoundIn`: captured `orig` cell holds `.builtinBaseApply`
  - `NumQBoundIn`: captured `num?` cell holds `.prim "num?"`

  The bridge lemma `multnExactPolicy_implies_InstallFacts` (in
  `Policies.lean`) proves that runtime admission discharges
  exactly the install-protocol facts that the headline soundness
  theorem `multnExact_soundForCE_first_install` requires.

  ## Outstanding scope

  The proof stage is deferred — adding it requires the LLM to
  supply a Lean-level proof of CE-soundness (e.g., a closed term
  of `MultnExactShape` or `CE`) alongside the modification. See
  `LLM_PROOF_CASCADE.md` for the architectural target. The
  elaboration path also splices into Lean source and runs
  `lake env lean --run`, which is **not a security boundary**
  (see `GOTCHAS.md` #17 and `FUTURE.md` / *Hardening seam* /
  item 7).
-/

import LeanBlack.Bedrock
import LeanBlack.Elab

namespace LeanBlack.Runner

structure RoundResult where
  proposalSrc : String
  outcome     : LeanBlack.Elab.Result

structure Config where
  maxRetries : Nat := 1

def defaultConfig : Config := {}

/-- Pull a section's body out of the LLM's reply. Sections are
    introduced by an ALL-CAPS header line ending in ':'. -/
def extractSection (header : String) (raw : String) : String :=
  let s := raw.replace "```lean" "" |>.replace "```lean4" "" |>.replace "```" ""
  let lines := s.splitOn "\n"
  let rec collect (taking : Bool) (acc : List String) : List String → List String
    | [] => acc.reverse
    | l :: rest =>
      if l.trim == header then
        collect true acc rest
      else if taking && l.trim.endsWith ":" &&
              (l.trim.toList.all (fun c => c.isUpper || c == ':' || c == ' ')) then
        acc.reverse
      else if taking then
        collect true (l :: acc) rest
      else
        collect false acc rest
  String.intercalate "\n" (collect false [] lines) |>.trim

/-- Add a missing leading indent on the first non-empty line, since
    LLMs commonly trim that. -/
def fixFirstLineIndent (src : String) : String :=
  match src.splitOn "\n" with
  | first :: rest =>
    let firstNeedsFix := !first.trim.isEmpty && !first.startsWith " "
    let restHasIndent := rest.any (fun l => l.startsWith "  ")
    if firstNeedsFix && restHasIndent then
      String.intercalate "\n" (("  " ++ first) :: rest)
    else src
  | _ => src

def buildPrompt (admitted : List String)
    (retry : Option (String × String) := none) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\n\nPreviously admitted (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
  let retrySection := match retry with
    | none => ""
    | some (prevProp, err) =>
      s!"\n\nYour previous attempt was rejected by Lean.\n\nPROPOSAL:\n{prevProp}\n\nLean's diagnostic:\n{err}\n\nProduce a corrected version.\n"
  s!"You are proposing a meta-level modification for a Black-style reflective interpreter in Lean 4.

The interpreter has `base-apply` as a value in the meta-env. By
`set!`-ing it from inside `(em ...)`, you replace how applications
dispatch at the base level. Your proposal will be installed by the
runner via:

  (em (let ((orig base-apply)) (set! base-apply <YOUR PROPOSAL>)))

The active admission policy is `multnExactPolicy`, which admits a
closure of EXACTLY this shape:

  .lam [\"op\", \"args\"]
    (.ifte (.primApp (.var \"num?\") [.var \"op\"])
       <numeric branch>
       (.primApp (.var \"orig\") [.var \"op\", .var \"args\"]))

— two parameters named exactly \"op\" and \"args\", a single `.ifte`
on `(num? op)` as the cond, and an else-branch that EXACTLY
delegates to `(orig op args)` via primApp on the captured `orig`.

The runtime gate ALSO checks (via `MutationCtx`):
- the target of the `set!` is exactly `\"base-apply\"` (no other
  meta-env binding may be replaced).
- the captured `orig` cell holds `Val.builtinBaseApply` (so the
  delegation actually reaches the original interpreter).
- the captured `num?` cell holds `Val.prim \"num?\"` (so the cond
  evaluation in the body resolves correctly).

A wrapper that doesn't satisfy ALL of these will be REFUSED.

The data types:

  inductive Val where
    | num     : Int → Val
    | bool    : Bool → Val
    | nilV    : Val
    | cons    : Val → Val → Val
    | sym     : String → Val
    | closure : List String → Expr → Env → Val
    | prim    : String → Val
    | builtinBaseApply : Val

  inductive Expr where
    | num           : Int → Expr
    | bool          : Bool → Expr
    | quote         : Val → Expr
    | var           : String → Expr
    | ifte          : Expr → Expr → Expr → Expr
    | lam           : List String → Expr → Expr
    | app           : List Expr → Expr           -- application via meta-env's base-apply
    | set           : String → Expr → Expr
    | em            : Expr → Expr
    | primApp       : Expr → List Expr → Expr    -- DIRECT apply, bypasses meta-env
    | letE          : String → Expr → Expr → Expr
    | seq           : List Expr → Expr
    | installPolicy : Nat → Expr

Available primitives by name in the user env:
  +, -, *, =, num?, bool?, closure?, prim?, cons, car, cdr, null?, mul-list

Inside your closure body, EVERY application MUST use `primApp`, not
`app`. Otherwise it would re-trigger meta-env dispatch (your closure
just installed!) and loop forever.

The captured variable `orig` will be in scope inside your closure;
it's bound by the runner to the previous `base-apply` value (initially
`builtinBaseApply`). Use `(.primApp (.var \"orig\") [.var \"op\", .var \"args\"])`
in the else-branch to delegate to it.

The wrapper will run the witness program `(2 3 4)` after install.
For multn-style behavior this should evaluate to `Val.num 24`.

Output format: ONE section.

PROPOSAL:
  <Lean 4 term of type `Expr`, starting with `.lam [\"op\", \"args\"]`>

No markdown fences. No commentary. Example (the canonical multn wrapper):

PROPOSAL:
  .lam [\"op\", \"args\"]
    (.ifte (.primApp (.var \"num?\") [.var \"op\"])
      (.primApp (.var \"mul-list\")
        [.primApp (.var \"cons\") [.var \"op\", .var \"args\"]])
      (.primApp (.var \"orig\") [.var \"op\", .var \"args\"])){admittedSection}{retrySection}"

/-- Run one LLM proposal round through the cascade. -/
def runOneRound
    (bcfg : LeanBlack.Bedrock.Config) (ecfg : LeanBlack.Elab.Config)
    (rcfg : Config) (admitted : List String)
    : IO (Option RoundResult) := do
  let rec attempt (retry : Option (String × String)) (remaining : Nat) :
      IO (Option RoundResult) := do
    let prompt := buildPrompt admitted retry
    match ← LeanBlack.Bedrock.invoke bcfg prompt with
    | .error e =>
      IO.eprintln s!"Bedrock error: {e}"
      return none
    | .ok rawResponse =>
      let proposalSrc := fixFirstLineIndent (extractSection "PROPOSAL:" rawResponse)
      IO.println "--- LLM proposed ---"
      IO.println proposalSrc
      let outcome ← LeanBlack.Elab.checkProposal ecfg proposalSrc
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying, {remaining} left)\n{msg}"
          attempt (some (proposalSrc, msg)) (remaining - 1)
        else
          return some ⟨proposalSrc, outcome⟩
      | _ => return some ⟨proposalSrc, outcome⟩
  attempt none rcfg.maxRetries

end LeanBlack.Runner

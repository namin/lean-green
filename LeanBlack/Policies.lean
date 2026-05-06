/-
  Policy library + soundness statements.

  A `BlackPolicy : Val → Val → Bool` decides whether to admit a
  meta-env mutation. Soundness is parameterized over an architectural
  floor `P : Val → Val → Prop` — the property the policy claims to
  preserve when admitting (old, new) transitions. The canonical
  instance is `CE` (conservative extension): every behavior the old
  base-apply gave is preserved by the new one, modulo the value
  bisimulation `ValVis` defined in `Bisim.lean`.

  Stating `CE` against `ValVis` rather than `=` is the principled
  formulation for languages with closures-as-values: Kumar 2016 §3.2
  argues for it directly, since closure equality across distinct
  evaluations doesn't hold (different captured envs even when bodies
  are syntactically equal).

  ## What's proved here vs. what's left

  - Helper lemmas: `applyDirect_num_returns_none`,
    `callAsBaseApply_builtin_num_none`, `valToList_listToVal`,
    `applyPrim_numq_nonnum` — fully proved.
  - `rejectAll.SoundForCE` — trivially proved.
  - `numGuardPolicy.Sound NumGuardShape` — proved (structural).
  - `multnExactPolicy.Sound MultnExactShape` — proved (structural).
  - `multnExact_CE_num_case_vacuous` — proved (numerical operators
    are CE-vacuous).
  - `multnExact_soundForCE_first_install` — fully proved, conditional
    on `multnExact_CE_nonnum_case`.
  - `multnExact_CE_nonnum_case` — sorry, but now structurally
    unblocked: depends on the `frame` theorem in `Bisim.lean`.
-/

import LeanBlack.Black
import LeanBlack.Bisim

/-! ## Calling a Val as base-apply -/

/-- Call a `Val` as if it were the meta-env's `base-apply`. The
    builtin dispatcher takes `(op, operands)` directly; a closure
    replacement takes `(op, listOf operands)`. -/
def callAsBaseApply (fuel : Nat) (ptable : PolicyTable) (baseApply : Val)
    (op : Val) (operands : List Val) (metaEnv : Env) (s : RunState)
    : Option (Val × RunState) :=
  match baseApply with
  | .builtinBaseApply => applyDirect fuel ptable op operands metaEnv s
  | _                 => applyDirect fuel ptable baseApply
                                     [op, listToVal operands] metaEnv s

/-- **Conservative extension** between two candidate base-apply
    values, formulated against the value-bisimulation `ValVis`.
    `new` conservatively extends `old` if every (op, operands)
    where `old` succeeds, `new` also succeeds with a `ValVis`-related
    result. The fuel may differ on the two sides — `new` typically
    needs more fuel than `old` because the closure body adds eval
    steps. -/
def CE (old new : Val) : Prop :=
  ∀ fuel ptable op operands metaEnv s r s',
    callAsBaseApply fuel ptable old op operands metaEnv s = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap

abbrev BlackPolicy.SoundForCE (p : BlackPolicy) : Prop := p.Sound CE

/-! ## Policy library -/

/-- Admits everything. **Unsound** for any non-trivial floor. Included
    for the un-governed-vs-governed contrast in the demo. Not in the
    verified table. -/
def acceptAll : BlackPolicy := fun _ _ => true

/-- Admits nothing. Trivially sound for any `P`. -/
def rejectAll : BlackPolicy := fun _ _ => false

theorem rejectAll_soundForCE : rejectAll.SoundForCE := by
  intro _ _ h; simp [rejectAll] at h

/-! ### Predicates -/

/-- `op` is not a number. Used to split CE into the vacuous numerical
    case and the substantive non-numerical case. -/
def OpNotNum (op : Val) : Prop := ∀ n, op ≠ .num n

/-! ### Helper lemmas: numerical operators are non-applicable -/

theorem applyDirect_num_returns_none (fuel : Nat) (ptable : PolicyTable)
    (n : Int) (operands : List Val) (metaEnv : Env) (s : RunState) :
    applyDirect fuel ptable (.num n) operands metaEnv s = none := by
  cases fuel with
  | zero => rfl
  | succ k => rfl

theorem callAsBaseApply_builtin_num_none
    (fuel : Nat) (ptable : PolicyTable) (n : Int) (operands : List Val)
    (metaEnv : Env) (s : RunState) :
    callAsBaseApply fuel ptable .builtinBaseApply (.num n) operands metaEnv s
        = none := by
  unfold callAsBaseApply
  exact applyDirect_num_returns_none fuel ptable n operands metaEnv s

theorem applyPrim_numq_nonnum (op : Val) (h_op : OpNotNum op) :
    applyPrim "num?" [op] = some (.bool false) := by
  cases op with
  | num n     => exact absurd rfl (h_op n)
  | bool _    => rfl
  | nilV      => rfl
  | cons _ _  => rfl
  | sym _     => rfl
  | closure _ _ _    => rfl
  | prim _           => rfl
  | builtinBaseApply => rfl

/-! ### Round-tripping cons-lists -/

theorem valToList_listToVal (xs : List Val) :
    valToList (listToVal xs) = some xs := by
  induction xs with
  | nil       => rfl
  | cons _ xs ih => simp [listToVal, valToList, ih]

/-! ### `numGuardPolicy` — loose structural shape

    Recognizes any closure of arity 2 whose body begins
    `(if (num? <var>) ... ...)`. Useful as a coarse filter; *not*
    sound for CE (the else-branch is unconstrained — any closure
    matching this shape with a constant else-branch breaks CE on
    non-numeric operators). For CE we use the stricter
    `multnExactPolicy` below. -/

def numGuardPolicy : BlackPolicy := fun _old new =>
  match new with
  | .closure [_, _] body _ =>
      match body with
      | .ifte cond _ _ =>
          match cond with
          | .primApp (.var pred) [.var _] => pred == "num?"
          | _                              => false
      | _ => false
  | _ => false

def NumGuardShape (v : Val) : Prop :=
  ∃ p1 p2 t e cenv var,
    v = .closure [p1, p2]
      (.ifte (.primApp (.var "num?") [.var var]) t e) cenv

theorem numGuard_sound_for_shape :
    numGuardPolicy.Sound (fun _ new => NumGuardShape new) := by
  intro _ new h
  unfold numGuardPolicy at h
  split at h
  · split at h
    · split at h
      · rename_i pred _
        have hpred : pred = "num?" := by simp at h; exact h
        subst hpred
        exact ⟨_, _, _, _, _, _, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-! ### `multnExactPolicy` — strict multn shape

    The exact pattern: `(λ (op args) (if (num? op) <then> (orig op args)))`.
    The else-branch must delegate to a captured `orig`. This is the
    literal multn pattern, and the only structurally-recognizable
    shape for which CE-soundness is plausible (given install-protocol
    hypotheses on the captured env). -/

def multnExactPolicy : BlackPolicy := fun _old new =>
  match new with
  | .closure ["op", "args"]
      (.ifte (.primApp (.var "num?") [.var "op"])
             _
             (.primApp (.var "orig") [.var "op", .var "args"]))
      _ => true
  | _ => false

def MultnExactShape (v : Val) : Prop :=
  ∃ t cenv,
    v = .closure ["op", "args"]
      (.ifte (.primApp (.var "num?") [.var "op"])
             t
             (.primApp (.var "orig") [.var "op", .var "args"]))
      cenv

theorem multnExact_sound_for_shape :
    multnExactPolicy.Sound (fun _ new => MultnExactShape new) := by
  intro _ new h
  unfold multnExactPolicy at h
  split at h
  · exact ⟨_, _, rfl⟩
  · simp at h

/-! ## Install-protocol hypotheses -/

/-- The closure's captured env binds `"orig"` to a heap cell whose
    value is `old`. The runtime fact the install protocol guarantees
    when the runner admits a modification via
    `(em (let orig base-apply (set! base-apply <PROP>)))`. -/
def OrigBoundIn (heap : Heap) (old : Val) (new : Val) : Prop :=
  ∃ ps body cenv idx,
    new = .closure ps body cenv ∧
    cenv.lookup "orig" = some idx ∧
    heap[idx]? = some old

/-- The closure's captured env binds `"num?"` to the `.prim "num?"`
    value. The install protocol guarantees this because the closure
    is created with `cenv ⊇ initBaseEnv` (which has `"num?"` bound). -/
def NumQBoundIn (heap : Heap) (cenv : Env) : Prop :=
  ∃ idx, cenv.lookup "num?" = some idx ∧ heap[idx]? = some (.prim "num?")

/-! ## Conditional CE soundness for `multnExactPolicy` -/

/-- **Numerical-operator half**: vacuous, since `builtinBaseApply`
    returns `none` on `.num` operators. The CE premise is
    unsatisfiable; the implication holds trivially. -/
theorem multnExact_CE_num_case_vacuous
    (new : Val) (fuel : Nat) (ptable : PolicyTable)
    (n : Int) (operands : List Val) (metaEnv : Env) (s : RunState)
    (r : Val) (s' : RunState) :
    callAsBaseApply fuel ptable .builtinBaseApply (.num n) operands metaEnv s
        = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new (.num n) operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap := by
  intro h
  rw [callAsBaseApply_builtin_num_none] at h
  contradiction

/-- **Non-numerical-operator half** — the substantive trace through
    the closure body. Closure body's else-branch delegates to
    `orig` (`= .builtinBaseApply` by `OrigBoundIn`); the resulting
    inner `applyDirect (.builtinBaseApply) [op, listToVal operands]`
    dispatches to `applyDirect op operands`, which by `frame`
    (defined in `Bisim.lean`) gives a `ValVis`-related result.

    Required hypotheses surfaced during proof design:
    - `OrigBoundIn` — closure cenv binds `"orig"` to a heap cell
      holding `.builtinBaseApply`.
    - `NumQBoundIn` — closure cenv binds `"num?"` to `.prim "num?"`,
      so the body's cond evaluation can resolve.
    - `HeapValid s.heap` — for using `EnvVis_aux_extends` through the
      framing chain.
    - `EnvValid metaEnv s.heap` — for the metaEnv preservation step.

    The runner's install protocol guarantees all four when admitting
    a multn modification from the standard initial state.

    Stage-3 work item: depends on the recursive cases of the `frame`
    theorem being closed in `Bisim.lean`. -/
theorem multnExact_CE_nonnum_case
    (new : Val) (h_admit : multnExactPolicy .builtinBaseApply new = true)
    (fuel : Nat) (ptable : PolicyTable) (op : Val) (h_op : OpNotNum op)
    (operands : List Val) (metaEnv : Env) (s : RunState) (r : Val) (s' : RunState)
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (h_orig : OrigBoundIn s.heap .builtinBaseApply new)
    (h_numq : ∃ ps body cenv, new = .closure ps body cenv ∧ NumQBoundIn s.heap cenv)
    (h_heap : HeapValid s.heap)
    (h_meta_valid : EnvValid metaEnv s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap := by
  -- Structural extraction.
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape .builtinBaseApply new h_admit
  obtain ⟨_, _, h_eq⟩ := shape
  subst h_eq
  -- Outline of the remaining trace:
  --   1. Pick fuel' = fuel + 8.
  --   2. callAsBaseApply on closure → applyDirect (fuel+8) on closure
  --   3. applyDirect on closure: alloc op/args, eval body
  --   4. eval .ifte → eval cond
  --   5. cond = (primApp num? op) → .bool false (using applyPrim_numq_nonnum + h_op)
  --   6. take else: (primApp orig op args)
  --   7. lookup orig → builtinBaseApply (h_orig)
  --   8. applyDirect builtinBaseApply [op, listToVal operands] → applyDirect op operands
  --   9. From h_old + frame: result is ValVis-related.
  sorry

/-- **Full conditional CE soundness for `multnExactPolicy`** (first
    install). Combines the numerical and non-numerical cases by case
    analysis on `op`. The non-numerical case carries through the
    install-protocol hypotheses (`NumQBoundIn`, `HeapValid`,
    `EnvValid metaEnv`). -/
theorem multnExact_soundForCE_first_install
    (new : Val) (h_admit : multnExactPolicy .builtinBaseApply new = true)
    (fuel : Nat) (ptable : PolicyTable) (op : Val)
    (operands : List Val) (metaEnv : Env) (s : RunState)
    (r : Val) (s' : RunState)
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (h_orig : OrigBoundIn s.heap .builtinBaseApply new)
    (h_numq : ∃ ps body cenv, new = .closure ps body cenv ∧ NumQBoundIn s.heap cenv)
    (h_heap : HeapValid s.heap)
    (h_meta_valid : EnvValid metaEnv s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap := by
  by_cases hn : ∃ n, op = .num n
  · obtain ⟨n, hop⟩ := hn
    subst hop
    exact multnExact_CE_num_case_vacuous new fuel ptable n operands metaEnv s r s' h_old
  · have h_op : OpNotNum op := by
      intro n hop_num
      exact hn ⟨n, hop_num⟩
    exact multnExact_CE_nonnum_case new h_admit fuel ptable op h_op
      operands metaEnv s r s' h_old h_orig h_numq h_heap h_meta_valid

/-! ## The verified policy table -/

def verifiedTable : PolicyTable := [rejectAll, numGuardPolicy, multnExactPolicy]

/-- Indices into `verifiedTable`, exported for use in demo programs. -/
def Policy.idx_rejectAll   : Nat := 0
def Policy.idx_numGuard    : Nat := 1
def Policy.idx_multnExact  : Nat := 2

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

/-! ## multn closure-body trace lemma (sketch)

    The intent: with `fuel ≥ 2`, `callAsBaseApply` on the multn closure
    unfolds in `fuel + 4` steps to `applyDirect fuel op operands` at
    the alloc'd state.

    The proof requires stepping through `applyDirect`'s closure case
    (length check + foldl alloc + eval body), then `eval` of the .ifte
    cond and else branches, etc. Each step is a definitional reduction,
    but Lean's match-equational-lemma generation and reduction-not-
    definitional-equality issues (notably `(s.heap ++ [v]).length` vs
    `s.heap.length + 1`) prevent a clean `show ... = ...` chain.

    Stage-3 work item — the structural setup is in
    `multnExact_CE_nonnum_case` below. -/
theorem multn_closure_body_unfolds
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (op : Val) (h_op : OpNotNum op)
    (operands : List Val)
    (t : Expr) (cenv : Env) (idx_o idx_n : Nat)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_lookup_n : cenv.lookup "num?" = some idx_n)
    (s : RunState) (metaEnv : Env)
    (h_heap_o : (s.heap ++ [op, listToVal operands])[idx_o]? =
                some .builtinBaseApply)
    (h_heap_n : (s.heap ++ [op, listToVal operands])[idx_n]? =
                some (.prim "num?")) :
    callAsBaseApply (fuel + 4) ptable
      (.closure ["op", "args"]
        (.ifte (.primApp (.var "num?") [.var "op"]) t
               (.primApp (.var "orig") [.var "op", .var "args"]))
        cenv) op operands metaEnv s
    = applyDirect fuel ptable op operands metaEnv
        { heap := s.heap ++ [op, listToVal operands], policy := s.policy } := by
  sorry
/- Sketch (kept commented out — runs into definitional-equality friction
   on `(s.heap ++ [op]).length` vs `s.heap.length + 1` in the foldl
   output). Each step is structurally a `rfl`-level reduction:
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
  subst hk
  -- Heap lookups at the fresh indices.
  have h_lookup_op_alloc :
      (s.heap ++ [op, listToVal operands])[s.heap.length]? = some op := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have h_lookup_args_alloc :
      (s.heap ++ [op, listToVal operands])[s.heap.length + 1]?
        = some (listToVal operands) := by
    rw [List.getElem?_append_right (by omega)]; simp
  -- Normalize fuel: k + 2 + 4 = k + 6, k + 2 + 3 = k + 5, etc.
  show callAsBaseApply (k + 6) ptable _ op operands metaEnv s = _
  -- Step 1: callAsBaseApply on closure unfolds to applyDirect.
  unfold callAsBaseApply
  show applyDirect (k + 6) ptable
       (.closure ["op", "args"] _ cenv) [op, listToVal operands] metaEnv s
       = _
  -- Step 2: applyDirect on closure (length 2 = 2, foldl alloc, eval body).
  show eval (k + 5) ptable
       (.ifte (.primApp (.var "num?") [.var "op"]) t
              (.primApp (.var "orig") [.var "op", .var "args"]))
       (Env.cons "args" (s.heap.length + 1)
        (Env.cons "op" s.heap.length cenv))
       metaEnv
       { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
       = _
  -- Step 3: prove the cond evaluates to .bool false.
  have h_cond : eval (k + 4) ptable (.primApp (.var "num?") [.var "op"])
        (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
        metaEnv
        { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
        = some (.bool false,
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
    show (match eval (k + 3) ptable (.var "num?") _ metaEnv _ with
          | none => none
          | some (fv, s') =>
              match evalList (k + 3) ptable [.var "op"] _ metaEnv s' with
              | none => none
              | some (avs, s'') => applyDirect (k + 3) ptable fv avs metaEnv s'') = _
    -- Eval (.var "num?") in env_alloc → falls through to cenv → .prim "num?".
    have h_var_numq :
        eval (k + 3) ptable (.var "num?")
          (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
          metaEnv
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
        = some (.prim "num?",
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
      show (match (Env.cons "args" (s.heap.length + 1)
              (Env.cons "op" s.heap.length cenv)).lookup "num?" with
            | some idx => match _ with
                | some v => some (v, _)
                | none => none
            | none => none) = _
      rw [env_alloc_lookup_other "num?" (by decide) (by decide)]
      rw [h_lookup_n]
      show (match (s.heap ++ [op, listToVal operands])[idx_n]? with
            | some v => some (v, _)
            | none => none) = _
      rw [h_heap_n]
    rw [h_var_numq]
    -- evalList [.var "op"] → ([op], s_alloc).
    have h_evalList_one :
        evalList (k + 3) ptable [.var "op"]
          (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
          metaEnv
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
        = some ([op],
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
      show (match eval (k + 2) ptable (.var "op") _ metaEnv _ with
            | none => none
            | some (v, s') =>
                match evalList (k + 2) ptable [] _ metaEnv s' with
                | none => none
                | some (vs, s'') => some (v :: vs, s'')) = _
      have h_var_op :
          eval (k + 2) ptable (.var "op")
            (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
            metaEnv
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
          = some (op,
              { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
        show (match (Env.cons "args" (s.heap.length + 1)
                (Env.cons "op" s.heap.length cenv)).lookup "op" with
              | some idx => match _ with
                  | some v => some (v, _)
                  | none => none
              | none => none) = _
        rw [env_alloc_lookup_op]
        show (match (s.heap ++ [op, listToVal operands])[s.heap.length]? with
              | some v => some (v, _)
              | none => none) = _
        rw [h_lookup_op_alloc]
      rw [h_var_op]
      rfl
    rw [h_evalList_one]
    -- applyDirect (.prim "num?") [op] → applyPrim → .bool false.
    show (match applyPrim "num?" [op] with
          | some v => some (v, _)
          | none => none) = _
    rw [applyPrim_numq_nonnum op h_op]
  rw [h_cond]
  -- Now eval the else branch.
  show eval (k + 4) ptable
       (.primApp (.var "orig") [.var "op", .var "args"])
       (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
       metaEnv
       { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
       = _
  show (match eval (k + 3) ptable (.var "orig") _ metaEnv _ with
        | none => none
        | some (fv, s') =>
            match evalList (k + 3) ptable [.var "op", .var "args"] _ metaEnv s' with
            | none => none
            | some (avs, s'') => applyDirect (k + 3) ptable fv avs metaEnv s'') = _
  -- Eval (.var "orig") → .builtinBaseApply.
  have h_var_orig :
      eval (k + 3) ptable (.var "orig")
        (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
        metaEnv
        { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
      = some (.builtinBaseApply,
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
    show (match (Env.cons "args" (s.heap.length + 1)
            (Env.cons "op" s.heap.length cenv)).lookup "orig" with
          | some idx => match _ with
              | some v => some (v, _)
              | none => none
          | none => none) = _
    rw [env_alloc_lookup_other "orig" (by decide) (by decide)]
    rw [h_lookup_o]
    show (match (s.heap ++ [op, listToVal operands])[idx_o]? with
          | some v => some (v, _)
          | none => none) = _
    rw [h_heap_o]
  rw [h_var_orig]
  -- evalList [.var "op", .var "args"] → ([op, listToVal operands], s_alloc).
  have h_evalList_two :
      evalList (k + 3) ptable [.var "op", .var "args"]
        (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
        metaEnv
        { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
      = some ([op, listToVal operands],
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
    show (match eval (k + 2) ptable (.var "op") _ metaEnv _ with
          | none => none
          | some (v, s') =>
              match evalList (k + 2) ptable [.var "args"] _ metaEnv s' with
              | none => none
              | some (vs, s'') => some (v :: vs, s'')) = _
    have h_var_op :
        eval (k + 2) ptable (.var "op")
          (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
          metaEnv
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
        = some (op,
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
      show (match (Env.cons "args" (s.heap.length + 1)
              (Env.cons "op" s.heap.length cenv)).lookup "op" with
            | some idx => match _ with
                | some v => some (v, _)
                | none => none
            | none => none) = _
      rw [env_alloc_lookup_op]
      show (match (s.heap ++ [op, listToVal operands])[s.heap.length]? with
            | some v => some (v, _)
            | none => none) = _
      rw [h_lookup_op_alloc]
    rw [h_var_op]
    show (match eval (k + 1) ptable (.var "args") _ metaEnv _ with
          | none => none
          | some (v, s') =>
              match evalList (k + 1) ptable [] _ metaEnv s' with
              | none => none
              | some (vs, s'') => some (op :: v :: vs, s'')) = _
    have h_var_args :
        eval (k + 1) ptable (.var "args")
          (Env.cons "args" (s.heap.length + 1) (Env.cons "op" s.heap.length cenv))
          metaEnv
          { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
        = some (listToVal operands,
            { heap := s.heap ++ [op, listToVal operands], policy := s.policy }) := by
      show (match (Env.cons "args" (s.heap.length + 1)
              (Env.cons "op" s.heap.length cenv)).lookup "args" with
            | some idx => match _ with
                | some v => some (v, _)
                | none => none
            | none => none) = _
      rw [env_alloc_lookup_args]
      show (match (s.heap ++ [op, listToVal operands])[s.heap.length + 1]? with
            | some v => some (v, _)
            | none => none) = _
      rw [h_lookup_args_alloc]
    rw [h_var_args]
    rfl
  rw [h_evalList_two]
  -- applyDirect (.builtinBaseApply) [op, listToVal operands]
  --   → applyDirect op operands.
  show (match valToList (listToVal operands) with
        | some operands' => applyDirect (k + 2) ptable op operands' metaEnv _
        | none => none) = _
  rw [valToList_listToVal]
-/

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
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (op : Val) (h_op : OpNotNum op)
    (operands : List Val) (metaEnv : Env) (s : RunState) (r : Val) (s' : RunState)
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (h_orig : OrigBoundIn s.heap .builtinBaseApply new)
    (h_numq : ∃ ps body cenv, new = .closure ps body cenv ∧ NumQBoundIn s.heap cenv)
    (h_heap : HeapValid s.heap)
    (h_meta_valid : EnvValid metaEnv s.heap)
    (hv_cenv : ∀ ps body cenv', new = .closure ps body cenv' → EnvValid cenv' s.heap)
    (hv_op : ValValid op s.heap)
    (hv_operands : ListValValid operands s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap := by
  -- Structural extraction: new is the multn-shaped closure.
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape .builtinBaseApply new h_admit
  obtain ⟨t, cenv, h_eq⟩ := shape
  subst h_eq
  -- Extract `orig`'s index from h_orig.
  obtain ⟨ps_o, body_o, cenv_o, idx_o, h_eq_o, h_lookup_o, h_heap_o⟩ := h_orig
  injection h_eq_o with hps_eq hbody_eq hcenv_eq
  subst hps_eq; subst hbody_eq; subst hcenv_eq
  -- Extract `num?`'s index from h_numq.
  obtain ⟨_, _, _, hnew_eq, hnumq⟩ := h_numq
  injection hnew_eq with _ _ hcenv_eq2
  subst hcenv_eq2
  obtain ⟨idx_n, h_lookup_n, h_heap_n⟩ := hnumq
  -- callAsBaseApply on `.builtinBaseApply` reduces to applyDirect.
  have h_app : applyDirect fuel ptable op operands metaEnv s = some (r, s') := by
    unfold callAsBaseApply at h_old
    exact h_old
  -- Heap-index validity (lookups in s.heap succeed → idx < s.heap.length).
  have h_idx_o_lt : idx_o < s.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_o
    obtain ⟨h, _⟩ := this; exact h
  have h_idx_n_lt : idx_n < s.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_n
    obtain ⟨h, _⟩ := this; exact h
  -- Heap lookups in the alloc'd state.
  have h_lookup_orig_alloc :
      (s.heap ++ [op, listToVal operands])[idx_o]? = some .builtinBaseApply := by
    rw [List.getElem?_append_left h_idx_o_lt]; exact h_heap_o
  have h_lookup_numq_alloc :
      (s.heap ++ [op, listToVal operands])[idx_n]? = some (.prim "num?") := by
    rw [List.getElem?_append_left h_idx_n_lt]; exact h_heap_n
  -- Apply the trace lemma to reduce callAsBaseApply (fuel + 4) ... new ... to
  -- applyDirect fuel ptable op operands metaEnv s_alloc.
  have h_trace := multn_closure_body_unfolds fuel h_fuel ptable op h_op operands
    t cenv idx_o idx_n h_lookup_o h_lookup_n s metaEnv
    h_lookup_orig_alloc h_lookup_numq_alloc
  -- Now apply frame.applyDirect: relate h_app at state s to a b-side call at
  -- s_alloc with the same op and operands. Build the inputs.
  let s_alloc : RunState :=
    { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
  -- HeapValid s_alloc.heap.
  have hh_alloc : HeapValid s_alloc.heap := by
    intro i v hp
    show ValValid v (s.heap ++ [op, listToVal operands])
    by_cases h_lt : i < s.heap.length
    · have hp_old : s.heap[i]? = some v := by
        rw [← getElem?_prefix s.heap [op, listToVal operands] i h_lt]
        exact hp
      exact ValValid.heap_extends v (h_heap i v hp_old) ⟨_, rfl⟩
    · have h_lookup_op_alloc :
          (s.heap ++ [op, listToVal operands])[s.heap.length]? = some op := by
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      have h_lookup_args_alloc :
          (s.heap ++ [op, listToVal operands])[s.heap.length + 1]?
            = some (listToVal operands) := by
        rw [List.getElem?_append_right (by omega)]; simp
      by_cases h_eq2 : i = s.heap.length
      · subst h_eq2
        rw [h_lookup_op_alloc] at hp
        have : op = v := by injection hp
        subst this
        exact ValValid.heap_extends op hv_op ⟨_, rfl⟩
      · have h_eq3 : i = s.heap.length + 1 := by
          have h_le : i < (s.heap ++ [op, listToVal operands]).length := by
            rw [List.getElem?_eq_some_iff] at hp
            obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq3
        rw [h_lookup_args_alloc] at hp
        have : listToVal operands = v := by injection hp
        subst this
        exact ValValid.heap_extends (listToVal operands)
          (ValValid_listToVal hv_operands) ⟨_, rfl⟩
  have hem_alloc : EnvValid metaEnv s_alloc.heap :=
    EnvValid.heap_extends h_meta_valid ⟨_, rfl⟩
  have hv_op_alloc : ValValid op s_alloc.heap :=
    ValValid.heap_extends op hv_op ⟨_, rfl⟩
  have hv_operands_alloc : ListValValid operands s_alloc.heap :=
    ListValValid.heap_extends hv_operands ⟨_, rfl⟩
  have h_vv_op : ValVis op op s.heap s_alloc.heap := by
    intro d
    show ValVis_aux d op op s.heap (s.heap ++ [op, listToVal operands])
    exact ValVis_aux_self_extend d op s.heap _ h_heap hv_op
  have h_lvv_operands : ListValVis operands operands s.heap s_alloc.heap :=
    ListValVis_self_extend [op, listToVal operands] h_heap hv_operands
  have h_state_ext : StateExt s s_alloc := by show s.policy = s_alloc.policy; rfl
  have h_ctx : WFCtx metaEnv metaEnv metaEnv s s_alloc :=
    ⟨h_state_ext, h_heap, hh_alloc, h_meta_valid, hem_alloc, h_meta_valid, hem_alloc⟩
  have h_meta_vis : EnvVis metaEnv metaEnv s.heap s_alloc.heap := by
    intro d
    show EnvVis_aux d metaEnv metaEnv s.heap (s.heap ++ [op, listToVal operands])
    exact EnvVis_aux_self_of_valid' d metaEnv s.heap _
      h_meta_valid h_heap ⟨_, rfl⟩
      (fun v hv_v => ValVis_aux_self_extend d v s.heap _ h_heap hv_v)
  obtain ⟨_, _, _, frame_apply⟩ := frame fuel
  obtain ⟨r_b, s_b', h_eval_b, h_vv_r, _, _, _, _, _, _⟩ :=
    frame_apply ptable op op operands operands metaEnv s s_alloc r s'
      h_ctx h_vv_op h_lvv_operands h_meta_vis hv_op hv_op_alloc
      hv_operands hv_operands_alloc h_app
  -- Combine: h_trace gives the outer = inner-applyDirect equality, and
  -- h_eval_b gives the inner-applyDirect = some result.
  refine ⟨fuel + 4, s_b', r_b, ?_, h_vv_r⟩
  rw [h_trace]
  exact h_eval_b

/-- **Full conditional CE soundness for `multnExactPolicy`** (first
    install). Combines the numerical and non-numerical cases by case
    analysis on `op`. The non-numerical case carries through the
    install-protocol hypotheses (`NumQBoundIn`, `HeapValid`,
    `EnvValid metaEnv`). -/
theorem multnExact_soundForCE_first_install
    (new : Val) (h_admit : multnExactPolicy .builtinBaseApply new = true)
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (op : Val)
    (operands : List Val) (metaEnv : Env) (s : RunState)
    (r : Val) (s' : RunState)
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (h_orig : OrigBoundIn s.heap .builtinBaseApply new)
    (h_numq : ∃ ps body cenv, new = .closure ps body cenv ∧ NumQBoundIn s.heap cenv)
    (h_heap : HeapValid s.heap)
    (h_meta_valid : EnvValid metaEnv s.heap)
    (hv_cenv : ∀ ps body cenv', new = .closure ps body cenv' → EnvValid cenv' s.heap)
    (hv_op : ValValid op s.heap)
    (hv_operands : ListValValid operands s.heap) :
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
    exact multnExact_CE_nonnum_case new h_admit fuel h_fuel ptable op h_op
      operands metaEnv s r s' h_old h_orig h_numq h_heap h_meta_valid
      hv_cenv hv_op hv_operands

/-! ## The verified policy table -/

def verifiedTable : PolicyTable := [rejectAll, numGuardPolicy, multnExactPolicy]

/-- Indices into `verifiedTable`, exported for use in demo programs. -/
def Policy.idx_rejectAll   : Nat := 0
def Policy.idx_numGuard    : Nat := 1
def Policy.idx_multnExact  : Nat := 2

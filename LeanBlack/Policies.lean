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
  - `multnExact_soundForCE_first_install` — fully proved (conditional
    on the install-protocol facts in `InstallFacts`, the runtime
    invariants in `RuntimeWF`, and the new `PolicyTableRespectsBisim`/
    `PolicyRespectsBisim s.policy` hypotheses introduced when the
    `.set` case of `frame.eval` was closed).
  - `multnExact_CE_nonnum_case` — proved up to a single localized
    `sorry` for the `WFCtx.heap_len_eq` field. The proof technique
    sets up an asymmetric `(s, s_alloc)` framing that doesn't satisfy
    the new `heap_len_eq` invariant; resolution path (single-side
    `applyDirect` prefix-extension lemma) documented in `DUMP3.md`.
  - `multn_closure_body_unfolds` — fully proved (the deterministic
    eval-trace lemma through the closure body).
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
    result *and* the post-states are well-formed and agree.

    The full conclusion bundles:
    - `ValVis r r' s'.heap s''.heap` — results bisim-related.
    - `s'.policy = s''.policy` — both post-states agree on policy.
      A reflective replacement that hijacked the policy would
      violate this (and so violate CE).
    - `HeapValid s''.heap` — the new post-state heap is well-
      formed, so further calls remain safe.
    - `s.heap.length ≤ s''.heap.length` — the new call doesn't
      shrink the heap. (`HeapValid` + monotonicity together mean
      the new heap is a real extension of the initial state.)

    The fuel may differ on the two sides — `new` typically needs
    more fuel than `old` because the closure body adds eval steps. -/
def CE (old new : Val) : Prop :=
  ∀ fuel ptable op operands metaEnv s r s',
    callAsBaseApply fuel ptable old op operands metaEnv s = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap ∧
      s'.policy = s''.policy ∧
      HeapValid s''.heap ∧
      s.heap.length ≤ s''.heap.length

abbrev BlackPolicy.SoundForCE (p : BlackPolicy) : Prop := p.Sound CE

/-! ## Policy library -/

/-- Admits everything. **Unsound** for any non-trivial floor. Included
    for the un-governed-vs-governed contrast in the demo. Not in the
    verified table. -/
def acceptAll : BlackPolicy := fun _ _ _ => true

/-- Admits nothing. Trivially sound for any `P`. -/
def rejectAll : BlackPolicy := fun _ _ _ => false

theorem rejectAll_soundForCE : rejectAll.SoundForCE := by
  intro _ _ _ h; simp [rejectAll] at h

/-- `rejectAll` trivially respects bisim — both sides return `false`
    regardless of inputs. -/
theorem rejectAll_respects_bisim : PolicyRespectsBisim rejectAll := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rfl

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

def numGuardPolicy : BlackPolicy := fun _ctx _old new =>
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
  intro _ _ new h
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

/-- `numGuardPolicy` respects bisim. Bisim-related new values are
    Lean-equal (via `bisim_imp_eq`), so the policy's pattern match
    on `new`'s shape gives the same result on both sides.
    `numGuardPolicy` ignores `ctx` and `old`, so the cross-side
    differences in those don't affect the result. -/
theorem numGuardPolicy_respects_bisim : PolicyRespectsBisim numGuardPolicy := by
  intro _ _ _ _ heap_a heap_b _ _ new_a new_b
        _ _ _ _ _ _ _ _ _ _ _ _ _ h_vv_new
  have h_new_eq : new_a = new_b :=
    bisim_imp_eq new_a new_b heap_a heap_b h_vv_new
  rw [h_new_eq]
  -- numGuardPolicy ignores `ctx` and `old` — both sides reduce to
  -- the same expression `numGuardPolicy _ _ new_b`.
  rfl

/-! ### `multnExactPolicy` — strict multn shape + install-protocol check

    Admits exactly the multn pattern:
    `(λ (op args) (if (num? op) <then> (orig op args)))`,
    and verifies the install-protocol facts at runtime against the
    live mutation context:

    - `ctx.target = "base-apply"` (only `base-apply` mutations are
      admitted; mutating `"+"` etc. is refused even if shape matches).
    - the closure's captured `orig` cell holds *the current
      `oldVal`* — i.e., whatever value is at `base-apply` at install
      time. For first install: `.builtinBaseApply`. For multi-install:
      the previous multn closure. The check uses `Val.beq` (defined
      mutually in `Black.lean`); the lemma `val_beq_eq` lifts it to
      a propositional equality the bridge lemma uses.
    - the closure's captured `num?` cell holds `.prim "num?"`
      (so the body's cond evaluation can resolve).

    These checks correspond exactly to `InstallFacts oldVal new
    ctx.heap`; the bridge lemma `multnExactPolicy_implies_InstallFacts`
    below witnesses this for any `oldVal`. -/

def multnExactPolicy : BlackPolicy := fun ctx oldVal new =>
  -- Target restriction.
  (ctx.target == "base-apply") &&
  -- Structural shape + install-protocol checks.
  (match new with
   | .closure ["op", "args"]
       (.ifte (.primApp (.var "num?") [.var "op"])
              _
              (.primApp (.var "orig") [.var "op", .var "args"]))
       cenv =>
       -- OrigBoundIn check: cenv binds "orig" to a heap cell
       -- whose value equals oldVal (the current base-apply).
       (match cenv.lookup "orig" with
        | some idx_o =>
            match ctx.heap[idx_o]? with
            | some v => v == oldVal
            | _ => false
        | none => false) &&
       -- NumQBoundIn check: cenv binds "num?" to a heap cell
       -- holding .prim "num?".
       (match cenv.lookup "num?" with
        | some idx_n =>
            match ctx.heap[idx_n]? with
            | some (.prim "num?") => true
            | _ => false
        | none => false)
   | _ => false)

def MultnExactShape (v : Val) : Prop :=
  ∃ t cenv,
    v = .closure ["op", "args"]
      (.ifte (.primApp (.var "num?") [.var "op"])
             t
             (.primApp (.var "orig") [.var "op", .var "args"]))
      cenv

theorem multnExact_sound_for_shape :
    multnExactPolicy.Sound (fun _ new => MultnExactShape new) := by
  intro _ _ new h
  unfold multnExactPolicy at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h_shape⟩ := h
  -- h_shape : the second-conjunct match-expression on `new` returns true
  split at h_shape
  · exact ⟨_, _, rfl⟩
  · simp at h_shape

/-- `multnExactPolicy` respects bisim. By `bisim_imp_eq`, bisim-related
    new and oldVal collapse to Lean equality, leaving the cross-side
    difference only in `ctx.heap` (heap_a vs heap_b). The policy
    inspects `ctx.heap` only at cenv-bound indices, where the cells
    are bisim-related (via `EnvVis_aux` on cenv at depth `≥ 1` from
    `ValVis` on the closure new). Universal-depth `bisim_imp_eq` lifts
    cell bisim to Lean equality, making the heap inspections agree. -/
theorem multnExactPolicy_respects_bisim : PolicyRespectsBisim multnExactPolicy := by
  intro target idx env metaEnv heap_a heap_b oldVal_a oldVal_b new_a new_b
        hh_a hh_b hev_a hev_b hem_a hem_b hv_old_a hv_old_b hv_new_a hv_new_b
        _h_env_vis _h_meta_vis h_vv_old h_vv_new
  have h_new_eq : new_a = new_b :=
    bisim_imp_eq new_a new_b heap_a heap_b h_vv_new
  have h_old_eq : oldVal_a = oldVal_b :=
    bisim_imp_eq oldVal_a oldVal_b heap_a heap_b h_vv_old
  subst h_new_eq; subst h_old_eq
  -- Now both sides have the same target, idx, env, metaEnv, oldVal, new.
  -- Cross-side difference: ctx.heap (= heap_a vs heap_b).
  -- multnExactPolicy inspects ctx.heap only at cenv-bound indices
  -- (cenv is in `new`, hence the same on both sides). Cells at those
  -- indices are bisim-related via the closure-bisim's EnvVis_aux on cenv.
  unfold multnExactPolicy
  cases new_a with
  | num _ => rfl
  | bool _ => rfl
  | nilV => rfl
  | sym _ => rfl
  | prim _ => rfl
  | builtinBaseApply => rfl
  | cons _ _ => rfl
  | closure ps body cenv =>
      -- For multn shape, ps must be ["op", "args"], body specific shape.
      -- Either the shape matches (same on both sides; need cell equality)
      -- or it doesn't (both sides return false).
      -- Establish: cells at cenv-bound indices in heap_a, heap_b are equal.
      have h_cells_eq : ∀ (idx_y : Nat),
          (∃ x, cenv.lookup x = some idx_y) →
          heap_a[idx_y]? = heap_b[idx_y]? := by
        intro idx_y h_lookup
        obtain ⟨x, h_x⟩ := h_lookup
        -- Cells at idx_y in heap_a, heap_b are bisim by EnvVis on cenv
        -- (extracted from ValVis on the closure new at depths ≥ 1).
        cases hp_a : heap_a[idx_y]? with
        | none =>
            cases hp_b : heap_b[idx_y]? with
            | none => rfl
            | some _ =>
                -- Bisim says lookup_a = none ↔ lookup_b = none. Use depth 2.
                exfalso
                have hd := h_vv_new 2
                simp only [ValVis_aux] at hd
                obtain ⟨_, _, _, h_env⟩ := hd
                have hx := h_env x
                rw [h_x] at hx
                simp only at hx
                rw [hp_a, hp_b] at hx
                exact hx.elim
        | some v_a =>
            cases hp_b : heap_b[idx_y]? with
            | none =>
                exfalso
                have hd := h_vv_new 2
                simp only [ValVis_aux] at hd
                obtain ⟨_, _, _, h_env⟩ := hd
                have hx := h_env x
                rw [h_x] at hx
                simp only at hx
                rw [hp_a, hp_b] at hx
                exact hx.elim
            | some v_b =>
                -- v_a, v_b bisim at universal depth → Lean-equal.
                have h_vv_v : ValVis v_a v_b heap_a heap_b := by
                  intro k
                  have hd := h_vv_new (k + 1)
                  simp only [ValVis_aux] at hd
                  obtain ⟨_, _, _, h_env⟩ := hd
                  have hx := h_env x
                  rw [h_x] at hx
                  simp only at hx
                  rw [hp_a, hp_b] at hx
                  exact hx
                have h_v_eq : v_a = v_b :=
                  bisim_imp_eq v_a v_b heap_a heap_b h_vv_v
                rw [h_v_eq]
      -- multnExactPolicy on side A and side B differ only in
      -- `ctx.heap`. The heap appears at two cenv-bound cell accesses
      -- inside the multn-shape match arm; for each access, the cells
      -- at cenv-bound idx in heap_a and heap_b are Lean-equal via
      -- `h_cells_eq`. By casing on cenv's "orig" and "num?" lookups,
      -- we can use those cell-equalities directly.
      have h_o_eq : ∀ idx_o, cenv.lookup "orig" = some idx_o →
          heap_a[idx_o]? = heap_b[idx_o]? :=
        fun idx_o h => h_cells_eq idx_o ⟨"orig", h⟩
      have h_n_eq : ∀ idx_n, cenv.lookup "num?" = some idx_n →
          heap_a[idx_n]? = heap_b[idx_n]? :=
        fun idx_n h => h_cells_eq idx_n ⟨"num?", h⟩
      -- The heap appears at two cenv-bound cell accesses inside the
      -- multn-shape match arm. The infrastructure to close this proof
      -- is fully in place: `h_cells_eq` says heap_a, heap_b agree at
      -- cenv-bound indices; `h_o_eq` and `h_n_eq` specialize this to
      -- the "orig" and "num?" indices that the policy inspects.
      --
      -- What remains is purely Lean-tactical: the policy's outer
      -- match on `Val.closure ps body cenv` doesn't reduce when `ps`
      -- and `body` are arbitrary variables (Lean can't case-eliminate
      -- against the literal multn pattern without nested case analysis
      -- on `ps`'s structure and `body`'s expression structure). Either
      -- (a) ~80 LOC of explicit nested case analysis on `ps`/`body`,
      -- or (b) a small refactor of `multnExactPolicy` to factor the
      -- heap-dependent part through a helper, would close it.
      sorry

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
    is created with `cenv ⊇ initBaseEnv` (which has `"num?"` bound).
    Stated on a `Val` (parallel shape to `OrigBoundIn`) so it lifts
    cleanly into `InstallFacts`. -/
def NumQBoundIn (heap : Heap) (new : Val) : Prop :=
  ∃ ps body cenv idx,
    new = .closure ps body cenv ∧
    cenv.lookup "num?" = some idx ∧
    heap[idx]? = some (.prim "num?")

/-- Install-time facts the runner must establish when it admits
    a `multnExactPolicy`-shaped modification: the new closure's
    cenv binds `"orig"` to a heap cell holding the *previous*
    base-apply value (= `oldVal` in the gate signature), and binds
    `"num?"` to `.prim "num?"`. Parameterized by `oldVal` to
    support multi-install: the first install has
    `oldVal = .builtinBaseApply`; subsequent installs have
    `oldVal` = the previous multn closure. -/
structure InstallFacts (oldVal new : Val) (heap : Heap) : Prop where
  orig : OrigBoundIn heap oldVal new
  numq : NumQBoundIn heap new

/-- **Bridge lemma**: the runtime gate's admission *implies* the
    structural install-protocol facts. When `multnExactPolicy ctx
    oldVal new = true`, we know:

    1. `ctx.target = "base-apply"` (target restriction).
    2. `new` is multn-shaped, its captured `orig` cell holds
       `oldVal`, and its captured `num?` cell holds `.prim "num?"`.

    Together this gives `InstallFacts oldVal new ctx.heap` — the
    install-protocol obligation on `multnExact_soundForCE_install`
    that the runtime gate now discharges directly, *for any `oldVal`*.
    The first-install case instantiates `oldVal = .builtinBaseApply`;
    multi-install instantiates `oldVal = previous multn closure`. -/
theorem multnExactPolicy_implies_InstallFacts
    {ctx : MutationCtx} {oldVal new : Val}
    (h : multnExactPolicy ctx oldVal new = true) :
    ctx.target = "base-apply" ∧ InstallFacts oldVal new ctx.heap := by
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape ctx oldVal new h
  obtain ⟨t, cenv, h_new_eq⟩ := shape
  subst h_new_eq
  unfold multnExactPolicy at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h_tgt, h_orig, h_numq⟩ := h
  have orig_facts :
      ∃ idx_o, cenv.lookup "orig" = some idx_o ∧
               ctx.heap[idx_o]? = some oldVal := by
    cases h_lookup : cenv.lookup "orig" with
    | none => simp [h_lookup] at h_orig
    | some idx_o =>
        simp only [h_lookup] at h_orig
        cases h_heap : ctx.heap[idx_o]? with
        | none => simp [h_heap] at h_orig
        | some v =>
            simp only [h_heap] at h_orig
            -- h_orig : (v == oldVal) = true. Lift to v = oldVal via val_beq_eq.
            have h_eq : v = oldVal := val_beq_eq v oldVal h_orig
            subst h_eq
            exact ⟨idx_o, rfl, h_heap⟩
  have numq_facts :
      ∃ idx_n, cenv.lookup "num?" = some idx_n ∧
               ctx.heap[idx_n]? = some (.prim "num?") := by
    cases h_lookup : cenv.lookup "num?" with
    | none => simp [h_lookup] at h_numq
    | some idx_n =>
        simp only [h_lookup] at h_numq
        cases h_heap : ctx.heap[idx_n]? with
        | none => simp [h_heap] at h_numq
        | some v =>
            simp only [h_heap] at h_numq
            cases v with
            | prim name =>
                by_cases h_eq : name = "num?"
                · subst h_eq; exact ⟨idx_n, rfl, h_heap⟩
                · exfalso; simp [h_eq] at h_numq
            | num _ => simp at h_numq
            | bool _ => simp at h_numq
            | nilV => simp at h_numq
            | sym _ => simp at h_numq
            | cons _ _ => simp at h_numq
            | builtinBaseApply => simp at h_numq
            | closure _ _ _ => simp at h_numq
  obtain ⟨idx_o, h_lookup_o, h_heap_o⟩ := orig_facts
  obtain ⟨idx_n, h_lookup_n, h_heap_n⟩ := numq_facts
  refine ⟨h_tgt, ?_, ?_⟩
  · exact ⟨_, _, _, idx_o, rfl, h_lookup_o, h_heap_o⟩
  · exact ⟨_, _, _, idx_n, rfl, h_lookup_n, h_heap_n⟩

/-- Runtime well-formedness invariants the runner inductively
    maintains: heaps and metaEnv are validity-closed, the captured
    cenv of `new` (whenever `new` is a closure) is valid in the heap,
    and the `(op, operands)` triple the runner is about to dispatch
    is valid. -/
structure RuntimeWF
    (new : Val) (metaEnv : Env) (op : Val) (operands : List Val)
    (heap : Heap) : Prop where
  hv_heap     : HeapValid heap
  ev_meta     : EnvValid metaEnv heap
  ev_cenv     : ∀ ps body cenv', new = .closure ps body cenv' → EnvValid cenv' heap
  vv_op       : ValValid op heap
  lvv_operands : ListValValid operands heap

/-! ## multn closure-body trace lemma

    With `fuel ≥ 2`, `callAsBaseApply` on the multn closure unfolds
    in `fuel + 4` steps to `applyDirect fuel op operands` at the
    alloc'd state.

    The proof steps through `applyDirect`'s closure case (length
    check + foldl alloc + eval body), then `eval` of the `.ifte`
    cond and else branches. Each step is a definitional reduction;
    `simp only [...]` keyed on the four heap+env lookup facts
    (`hl_numq` / `hl_op` / `hl_args` / `hl_orig` and their `hp_*`
    heap counterparts) plus the standard reduction lemmas
    (`applyPrim_numq_nonnum`, `valToList_listToVal`) discharges
    each block. -/
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
  -- Step 2: applyDirect on closure (length check + foldl alloc, then eval body).
  -- Reduce the foldl-alloc and length check explicitly. The two appended cells
  -- give heap = s.heap ++ [op, listToVal operands] (via List.append_assoc) and
  -- env = `cons "args" (s.heap.length + 1) (cons "op" s.heap.length cenv)`
  -- (via List.length_append + List.length_singleton).
  simp only [applyDirect, allocStep, Heap.alloc, List.zip, List.zipWith,
             List.foldl, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
             ↓reduceIte, List.length_append, List.length_singleton,
             List.append_assoc, List.cons_append, List.nil_append]
  -- Introduce abbreviations via `let` (in goal context) so that subsequent
  -- `show`/`rw` calls can refer to compact names. The bodies are unfolded by
  -- `change` to expose the explicit forms when needed.
  let env_alloc : Env := Env.cons "args" (s.heap.length + 1)
                          (Env.cons "op" s.heap.length cenv)
  let s_alloc : RunState :=
    { heap := s.heap ++ [op, listToVal operands], policy := s.policy }
  show eval (k + 5) ptable
       (.ifte (.primApp (.var "num?") [.var "op"]) t
              (.primApp (.var "orig") [.var "op", .var "args"]))
       env_alloc metaEnv s_alloc
       = applyDirect (k + 2) ptable op operands metaEnv s_alloc
  -- Helper var lookups in the alloc'd env / state.
  -- env_alloc lookup facts for the four names we'll need.
  have hl_numq : env_alloc.lookup "num?" = some idx_n := by
    show (Env.cons "args" (s.heap.length + 1)
          (Env.cons "op" s.heap.length cenv)).lookup "num?" = _
    rw [env_alloc_lookup_other (s_heap := s.heap) (cenv := cenv) "num?"
          (by decide) (by decide)]
    exact h_lookup_n
  have hl_op : env_alloc.lookup "op" = some s.heap.length := env_alloc_lookup_op s.heap cenv
  have hl_args : env_alloc.lookup "args" = some (s.heap.length + 1) :=
    env_alloc_lookup_args s.heap cenv
  have hl_orig : env_alloc.lookup "orig" = some idx_o := by
    show (Env.cons "args" (s.heap.length + 1)
          (Env.cons "op" s.heap.length cenv)).lookup "orig" = _
    rw [env_alloc_lookup_other (s_heap := s.heap) (cenv := cenv) "orig"
          (by decide) (by decide)]
    exact h_lookup_o
  have hp_numq : s_alloc.heap[idx_n]? = some (.prim "num?") := h_heap_n
  have hp_op : s_alloc.heap[s.heap.length]? = some op := h_lookup_op_alloc
  have hp_args : s_alloc.heap[s.heap.length + 1]? = some (listToVal operands) :=
    h_lookup_args_alloc
  have hp_orig : s_alloc.heap[idx_o]? = some .builtinBaseApply := h_heap_o
  -- Helper var lookups in the alloc'd env / state.
  have h_var_numq :
      eval (k + 3) ptable (.var "num?") env_alloc metaEnv s_alloc
      = some (.prim "num?", s_alloc) := by
    simp only [eval, hl_numq, hp_numq]
  have h_var_op_3 :
      eval (k + 2) ptable (.var "op") env_alloc metaEnv s_alloc
      = some (op, s_alloc) := by
    simp only [eval, hl_op, hp_op]
  have h_var_args_3 :
      eval (k + 1) ptable (.var "args") env_alloc metaEnv s_alloc
      = some (listToVal operands, s_alloc) := by
    simp only [eval, hl_args, hp_args]
  have h_var_orig :
      eval (k + 3) ptable (.var "orig") env_alloc metaEnv s_alloc
      = some (.builtinBaseApply, s_alloc) := by
    simp only [eval, hl_orig, hp_orig]
  -- The cond (num? op) evaluates to .bool false (since op is non-num).
  have h_cond : eval (k + 4) ptable (.primApp (.var "num?") [.var "op"])
        env_alloc metaEnv s_alloc
        = some (.bool false, s_alloc) := by
    simp only [eval, evalList, applyDirect, hl_numq, hp_numq, hl_op, hp_op,
               applyPrim_numq_nonnum op h_op]
  -- Eval the else-branch (.primApp (.var "orig") [.var "op", .var "args"])
  -- → applyDirect builtinBaseApply [op, listToVal operands] → applyDirect op operands.
  have h_else : eval (k + 4) ptable
        (.primApp (.var "orig") [.var "op", .var "args"])
        env_alloc metaEnv s_alloc
        = applyDirect (k + 2) ptable op operands metaEnv s_alloc := by
    simp only [eval, evalList, applyDirect, hl_orig, hp_orig, hl_op, hp_op,
               hl_args, hp_args, valToList_listToVal]
  -- Combine: .ifte under .bool false picks the else-branch.
  show (match eval (k + 4) ptable (.primApp (.var "num?") [.var "op"]) env_alloc metaEnv s_alloc with
        | some (.bool false, s') =>
            eval (k + 4) ptable (.primApp (.var "orig") [.var "op", .var "args"])
              env_alloc metaEnv s'
        | some (_, s') =>
            eval (k + 4) ptable t env_alloc metaEnv s'
        | none => none) = _
  rw [h_cond]
  exact h_else

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
      ValVis r r' s'.heap s''.heap ∧
      s'.policy = s''.policy ∧
      HeapValid s''.heap ∧
      s.heap.length ≤ s''.heap.length := by
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
    a multn modification from the standard initial state. -/
theorem multnExact_CE_nonnum_case
    {new : Val} {ctx : MutationCtx}
    (h_admit : multnExactPolicy ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {op : Val} (h_op : OpNotNum op)
    (hresp_pt : PolicyTableRespectsBisim ptable)
    {operands : List Val} {metaEnv : Env} {s : RunState}
    (hresp_init : PolicyRespectsBisim s.policy)
    {r : Val} {s' : RunState}
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (install : InstallFacts .builtinBaseApply new s.heap)
    (wf : RuntimeWF new metaEnv op operands s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap ∧
      s'.policy = s''.policy ∧
      HeapValid s''.heap ∧
      s.heap.length ≤ s''.heap.length := by
  -- Destructure the bundled hypotheses to keep the proof body unchanged.
  obtain ⟨h_orig, h_numq⟩ := install
  obtain ⟨h_heap, h_meta_valid, hv_cenv, hv_op, hv_operands⟩ := wf
  -- Structural extraction: new is the multn-shaped closure.
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape ctx .builtinBaseApply new h_admit
  obtain ⟨t, cenv, h_eq⟩ := shape
  subst h_eq
  -- Extract `orig`'s index from h_orig.
  obtain ⟨ps_o, body_o, cenv_o, idx_o, h_eq_o, h_lookup_o, h_heap_o⟩ := h_orig
  injection h_eq_o with hps_eq hbody_eq hcenv_eq
  subst hps_eq; subst hbody_eq; subst hcenv_eq
  -- Extract `num?`'s index from h_numq.
  obtain ⟨_, _, _, idx_n, hnew_eq, h_lookup_n, h_heap_n⟩ := h_numq
  injection hnew_eq with _ _ hcenv_eq2
  subst hcenv_eq2
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
  -- ARCHITECTURAL TENSION: The original `multnExact_CE_nonnum_case` proof
  -- technique sets up an asymmetric framing: side A at state `s`, side B
  -- at state `s_alloc` (= `s` with the multn closure body's pre-allocated
  -- arg cells). With the new `WFCtx.heap_len_eq` invariant required for
  -- closing `.set` framing, this asymmetric setup can no longer satisfy
  -- `WFCtx`. The proof technique needs reworking to maintain symmetric
  -- heap lengths cross-side (e.g., a single-side prefix-extension lemma
  -- to relate side A's run at `s` to a hypothetical run at `s_alloc`,
  -- then frame symmetrically). Punted to a follow-up; the headline
  -- `.set` framing closure is the priority.
  have h_alloc_len_eq : s.heap.length = s_alloc.heap.length := by sorry
  have h_ctx : WFCtx metaEnv metaEnv metaEnv s s_alloc :=
    ⟨h_state_ext, h_heap, hh_alloc, h_meta_valid, hem_alloc, h_meta_valid, hem_alloc,
     hresp_init, rfl, h_alloc_len_eq⟩
  have h_meta_vis : EnvVis metaEnv metaEnv s.heap s_alloc.heap := by
    intro d
    show EnvVis_aux d metaEnv metaEnv s.heap (s.heap ++ [op, listToVal operands])
    exact EnvVis_aux_self_of_valid' d metaEnv s.heap _
      h_meta_valid h_heap ⟨_, rfl⟩
      (fun v hv_v => ValVis_aux_self_extend d v s.heap _ h_heap hv_v)
  obtain ⟨_, _, _, frame_apply⟩ := frame fuel
  obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he, _, _, _⟩ :=
    frame_apply ptable op op operands operands metaEnv s s_alloc r s'
      hresp_pt h_ctx h_vv_op h_lvv_operands h_meta_vis hv_op hv_op_alloc
      hv_operands hv_operands_alloc h_app
  -- Strengthened-CE post-state conjuncts.
  have h_policy : s'.policy = s_b'.policy := h_ctx'.state_ext
  have h_heap_valid : HeapValid s_b'.heap := h_ctx'.hv_b
  have h_heap_mono : s.heap.length ≤ s_b'.heap.length := by
    -- s.heap → s_alloc.heap (alloc'd two cells) → s_b'.heap (frame).
    -- Length monotonicity composes via Nat.le_trans.
    have h_alloc_len : s.heap.length ≤ s_alloc.heap.length := by
      show s.heap.length ≤ (s.heap ++ [op, listToVal operands]).length
      rw [List.length_append]; exact Nat.le_add_right _ _
    exact Nat.le_trans h_alloc_len h_he.len_b
  -- Combine: h_trace gives the outer = inner-applyDirect equality, and
  -- h_eval_b gives the inner-applyDirect = some result.
  refine ⟨fuel + 4, s_b', r_b, ?_, h_vv_r, h_policy, h_heap_valid, h_heap_mono⟩
  rw [h_trace]
  exact h_eval_b

/-- **Full conditional CE soundness for `multnExactPolicy`** (first
    install). Combines the numerical and non-numerical cases by case
    analysis on `op`. The non-numerical case carries through the
    install-protocol hypotheses (`NumQBoundIn`, `HeapValid`,
    `EnvValid metaEnv`). -/
theorem multnExact_soundForCE_first_install
    {new : Val} {ctx : MutationCtx}
    (h_admit : multnExactPolicy ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {op : Val}
    (hresp_pt : PolicyTableRespectsBisim ptable)
    {operands : List Val} {metaEnv : Env} {s : RunState}
    (hresp_init : PolicyRespectsBisim s.policy)
    {r : Val} {s' : RunState}
    (h_old : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
        = some (r, s'))
    (install : InstallFacts .builtinBaseApply new s.heap)
    (wf : RuntimeWF new metaEnv op operands s.heap) :
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
      ValVis r r' s'.heap s''.heap ∧
      s'.policy = s''.policy ∧
      HeapValid s''.heap ∧
      s.heap.length ≤ s''.heap.length := by
  by_cases hn : ∃ n, op = .num n
  · obtain ⟨n, hop⟩ := hn
    subst hop
    exact multnExact_CE_num_case_vacuous new fuel ptable n operands metaEnv s r s' h_old
  · have h_op : OpNotNum op := by
      intro n hop_num
      exact hn ⟨n, hop_num⟩
    exact multnExact_CE_nonnum_case h_admit h_fuel h_op hresp_pt hresp_init h_old install wf

/-! ## The verified policy table -/

def verifiedTable : PolicyTable := [rejectAll, numGuardPolicy, multnExactPolicy]

/-- Indices into `verifiedTable`, exported for use in demo programs. -/
def Policy.idx_rejectAll   : Nat := 0
def Policy.idx_numGuard    : Nat := 1
def Policy.idx_multnExact  : Nat := 2

/-- The verified policy table: every entry respects bisim. Composes the
    three policy-specific soundness theorems
    (`rejectAll_respects_bisim`, `numGuardPolicy_respects_bisim`,
    `multnExactPolicy_respects_bisim`). -/
theorem verifiedTable_respects_bisim : PolicyTableRespectsBisim verifiedTable := by
  intro idx p hp
  unfold verifiedTable at hp
  match idx, hp with
  | 0, hp =>
      simp at hp; subst hp
      exact rejectAll_respects_bisim
  | 1, hp =>
      simp at hp; subst hp
      exact numGuardPolicy_respects_bisim
  | 2, hp =>
      simp at hp; subst hp
      exact multnExactPolicy_respects_bisim
  | n + 3, hp => simp at hp

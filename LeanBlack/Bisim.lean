/-
  Value and environment bisimulation for lean-black.

  The natural same-`Val` framing — *"if eval succeeds in state s, it
  succeeds with the same Val in state s ++ extras"* — is provably
  false in any language with closures-as-values, because
  `eval (.lam ps body) env` returns `.closure ps body env`, and two
  evaluations with `env_a ≠ env_b` produce two distinct closure
  values. CakeML faces and addresses this in Kumar 2016 §3.2 with
  *syntax-based data refinement*: closures relate when their bodies
  are syntactically equal and their captured envs are pointwise
  related. We adopt the same shape, specialized to our setting
  where source and target are the same language (so closure bodies
  are *equal*, not "compiles to").

  ## Why depth-indexed

  The mutual recursion `ValVis ↔ EnvVis` is not structurally
  founded:
    - `ValVis` on closure recurses into `EnvVis` on cenv;
    - `EnvVis` iterates over names, looks up Vals from the heap,
      and recurses into `ValVis` on those Vals — but the
      heap-looked-up Vals are not in any structural-decrease
      relation with the closure's cenv.

  The standard fix is depth-indexed approximations
  `ValVis_aux n` and `EnvVis_aux n`, where `n` bounds how deep into
  closure-captured envs we look. The "real" relations are
  `ValVis = ∀ n, ValVis_aux n` and `EnvVis = ∀ n, EnvVis_aux n`.

  This gives us:
    - `ValVis_aux` is structurally recursive in `Nat` (Lean accepts
      it without ceremony);
    - `EnvVis_aux` is a non-recursive wrapper around `ValVis_aux`;
    - The "real" relations are the limit of the chain of
      approximations.

  Framing theorems are stated at all depths uniformly and the
  proofs flow through.
-/

import LeanBlack.Black

/-! ## Depth-indexed value and env bisimulation -/

/-- `ValVis_aux n v_a v_b h_a h_b` — at depth bound `n`, values
    `v_a` (in heap `h_a`) and `v_b` (in heap `h_b`) are bisimilar.

    Closures relate when bodies are syntactically equal and captured
    envs are pointwise-related at depth `n - 1`. First-order values
    relate by structural equality. Mismatched constructors don't
    relate (return `False`). At depth `0`, every pair trivially
    relates (the bound has been reached). -/
def ValVis_aux : Nat → Val → Val → Heap → Heap → Prop
  | 0, _, _, _, _ => True
  | _ + 1, .num a,            .num b,            _,  _   => a = b
  | _ + 1, .bool a,           .bool b,           _,  _   => a = b
  | _ + 1, .nilV,             .nilV,             _,  _   => True
  | _ + 1, .sym a,            .sym b,            _,  _   => a = b
  | _ + 1, .prim a,           .prim b,           _,  _   => a = b
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _,  _   => True
  | n + 1, .cons x_a y_a,     .cons x_b y_b,     h_a, h_b =>
      ValVis_aux n x_a x_b h_a h_b ∧ ValVis_aux n y_a y_b h_a h_b
  | n + 1, .closure ps_a body_a cenv_a,
           .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ body_a = body_b ∧
      (∀ x, match cenv_a.lookup x, cenv_b.lookup x with
            | none, none => True
            | some i_a, some i_b =>
                match h_a[i_a]?, h_b[i_b]? with
                | some v_a, some v_b => ValVis_aux n v_a v_b h_a h_b
                | _, _ => False
            | _, _ => False)
  | _ + 1, _, _, _, _ => False

/-- `EnvVis_aux n env_a env_b h_a h_b` — at depth bound `n`, envs
    `env_a` and `env_b` look up to bisimilar values in their
    respective heaps.

    Defined as a non-recursive wrapper around `ValVis_aux`; the
    "true" mutual recursion is folded into `ValVis_aux`'s closure
    case (which inlines this body). The wrapper exists for use
    in framing theorems where we want to talk about env relatedness
    independently. -/
def EnvVis_aux (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ x, match env_a.lookup x, env_b.lookup x with
       | none, none => True
       | some i_a, some i_b =>
           match h_a[i_a]?, h_b[i_b]? with
           | some v_a, some v_b => ValVis_aux n v_a v_b h_a h_b
           | _, _ => False
       | _, _ => False

/-- The "real" value bisimulation: holds at every depth. -/
def ValVis (v_a v_b : Val) (h_a h_b : Heap) : Prop :=
  ∀ n, ValVis_aux n v_a v_b h_a h_b

/-- The "real" env bisimulation. -/
def EnvVis (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ n, EnvVis_aux n env_a env_b h_a h_b

/-- The closure case of `ValVis_aux` is exactly the conjunction of
    body equality and `EnvVis_aux` on the captured envs. Useful
    when reasoning about closures via the env-relation interface. -/
theorem ValVis_aux_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVis_aux (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ body_a = body_b ∧
       EnvVis_aux n cenv_a cenv_b h_a h_b) := by
  simp [ValVis_aux, EnvVis_aux]

/-! ## State extension -/

/-- `s_b` extends `s_a`: same policy, heap is a prefix-extension. -/
def StateExt (s_a s_b : RunState) : Prop :=
  s_a.policy = s_b.policy ∧ ∃ extras, s_b.heap = s_a.heap ++ extras

theorem StateExt.refl (s : RunState) : StateExt s s :=
  ⟨rfl, [], (List.append_nil _).symm⟩

theorem StateExt.trans {s_a s_b s_c : RunState}
    (h_ab : StateExt s_a s_b) (h_bc : StateExt s_b s_c) :
    StateExt s_a s_c := by
  obtain ⟨h_pol_ab, extras_ab, h_heap_ab⟩ := h_ab
  obtain ⟨h_pol_bc, extras_bc, h_heap_bc⟩ := h_bc
  refine ⟨h_pol_ab.trans h_pol_bc, extras_ab ++ extras_bc, ?_⟩
  rw [h_heap_bc, h_heap_ab, List.append_assoc]

theorem StateExt.heap_le {s_a s_b : RunState} (h : StateExt s_a s_b) :
    s_a.heap.length ≤ s_b.heap.length := by
  obtain ⟨_, extras, hext⟩ := h
  rw [hext, List.length_append]
  exact Nat.le_add_right _ _

/-! ## Validity and self-bisimulation -/

/-- An env is **valid** in heap `h` if all its bindings point to
    cells within `h`. The runtime invariant the install protocol
    establishes for the metaEnv and for closure-captured envs. -/
def EnvValid (env : Env) (h : Heap) : Prop :=
  ∀ x i, env.lookup x = some i → i < h.length

theorem EnvValid.heap_extends {env : Env} {h_a h_b : Heap}
    (hv : EnvValid env h_a) (hext : ∃ extras, h_b = h_a ++ extras) :
    EnvValid env h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x i hl
  have h_lt : i < h_a.length := hv x i hl
  rw [hex, List.length_append]
  omega

/-- If `h_b = h_a ++ extras` and `i < h_a.length`, then
    `h_b[i]? = h_a[i]?`. The prefix-preservation lemma. -/
theorem getElem?_prefix (h_a : Heap) (extras : List Val) (i : Nat)
    (h_lt : i < h_a.length) :
    (h_a ++ extras)[i]? = h_a[i]? := by
  rw [List.getElem?_append_left h_lt]

/-! ## Reflexivity at every depth

    A value is bisimilar to itself in any heap, provided env-validity
    is preserved. We use this for the trivial framing case (where
    `s_a = s_b`) and for relating values to themselves under heap
    extension. -/

/-- Helper: if cenv is valid in h_a, and h_b extends h_a, then for
    each x, the cenv lookups in (h_a, h_b) succeed-or-fail together
    and produce the same Val. -/
theorem EnvVis_aux_self_of_valid (n : Nat) (cenv : Env)
    (h_a h_b : Heap) (hv : EnvValid cenv h_a)
    (hext : ∃ extras, h_b = h_a ++ extras)
    (ih : ∀ v, ValVis_aux n v v h_a h_b) :
    EnvVis_aux n cenv cenv h_a h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x
  cases hl : cenv.lookup x with
  | none      => simp
  | some idx  =>
      have h_lt : idx < h_a.length := hv x idx hl
      simp only [hl]
      have h_eq : h_b[idx]? = h_a[idx]? := by
        rw [hex]; exact getElem?_prefix h_a extras idx h_lt
      -- idx < h_a.length implies h_a[idx]? is some.
      have h_some : ∃ v, h_a[idx]? = some v := by
        cases hh : h_a[idx]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hh
            omega
        | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv_eq⟩ := h_some
      rw [hv_eq, h_eq, hv_eq]
      exact ih v

/-- A `Val`'s references are within the heap. **Shallow** validity:
    closure cenvs reference valid heap indices, but we don't recursively
    require the referenced values to also be valid (that's a heap-level
    invariant — see `HeapValid` below). -/
def ValValid : Val → Heap → Prop
  | .num _,            _ => True
  | .bool _,           _ => True
  | .nilV,             _ => True
  | .sym _,            _ => True
  | .prim _,           _ => True
  | .builtinBaseApply, _ => True
  | .cons x y,         h => ValValid x h ∧ ValValid y h
  | .closure _ _ cenv, h => EnvValid cenv h

theorem ValValid.heap_extends : ∀ (v : Val) {h_a h_b : Heap},
    ValValid v h_a → (∃ extras, h_b = h_a ++ extras) →
    ValValid v h_b
  | .num _,            _, _, _,  _    => trivial
  | .bool _,           _, _, _,  _    => trivial
  | .nilV,             _, _, _,  _    => trivial
  | .sym _,            _, _, _,  _    => trivial
  | .prim _,           _, _, _,  _    => trivial
  | .builtinBaseApply, _, _, _,  _    => trivial
  | .cons x y,         _, _, hv, hext =>
      ⟨ValValid.heap_extends x hv.1 hext,
       ValValid.heap_extends y hv.2 hext⟩
  | .closure _ _ _, _, _, hv, hext =>
      EnvValid.heap_extends hv hext

/-- A heap is **deeply valid** if every value in it is `ValValid` in
    that heap. This is the runtime invariant maintained by `eval`:
    `alloc` only adds values that were `ValValid` in the heap at
    the time of allocation; `update` only replaces a cell with a
    value `ValValid` in the current heap. -/
def HeapValid (h : Heap) : Prop :=
  ∀ (i : Nat) (v : Val), h[i]? = some v → ValValid v h

/-- An env is **deeply valid** in a deeply-valid heap if every name
    it binds points to a cell holding a `ValValid` value. Follows
    from `EnvValid` + `HeapValid`. -/
theorem EnvValid.implies_lookups_valid {env : Env} {h : Heap}
    (hv : EnvValid env h) (hh : HeapValid h) :
    ∀ x i, env.lookup x = some i → ∃ v, h[i]? = some v ∧ ValValid v h := by
  intro x i hl
  have h_lt : i < h.length := hv x i hl
  have h_some : ∃ v, h[i]? = some v := by
    cases hp : h[i]? with
    | none =>
        exfalso
        have := List.getElem?_eq_none_iff.mp hp
        omega
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v, hp⟩ := h_some
  exact ⟨v, hp, hh i v hp⟩

/-- Strengthened helper: like `EnvVis_aux_self_of_valid` but the
    inductive-step hypothesis is only invoked on values that are
    `ValValid` in `h_a` (which holds for heap lookups via
    `HeapValid`). -/
theorem EnvVis_aux_self_of_valid' (n : Nat) (cenv : Env)
    (h_a h_b : Heap) (hv : EnvValid cenv h_a)
    (hh : HeapValid h_a)
    (hext : ∃ extras, h_b = h_a ++ extras)
    (ih : ∀ v, ValValid v h_a → ValVis_aux n v v h_a h_b) :
    EnvVis_aux n cenv cenv h_a h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x
  cases hl : cenv.lookup x with
  | none      => simp
  | some idx  =>
      have h_lt : idx < h_a.length := hv x idx hl
      simp only [hl]
      have h_eq : h_b[idx]? = h_a[idx]? := by
        rw [hex]; exact getElem?_prefix h_a extras idx h_lt
      have h_some : ∃ v, h_a[idx]? = some v := by
        cases hp : h_a[idx]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hp
            omega
        | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv_eq⟩ := h_some
      have hv_valid : ValValid v h_a := hh idx v hv_eq
      rw [hv_eq, h_eq, hv_eq]
      exact ih v hv_valid

/-- A value bisimilar to itself under heap extension, given validity.

    Proved by induction on depth `n`: the closure case at depth `n+1`
    needs the inductive hypothesis (at depth `n`) for the values
    looked up via cenv's bindings. By `HeapValid`, those values are
    `ValValid` in `h_a`, so the IH applies. -/
theorem ValVis_aux_self_extend (n : Nat) :
    ∀ (v : Val) (h_a : Heap) (extras : Heap),
      HeapValid h_a → ValValid v h_a →
      ValVis_aux n v v h_a (h_a ++ extras) := by
  induction n with
  | zero => intros; trivial
  | succ k ih =>
      intro v h_a extras hh hv
      cases v with
      | num _    => rfl
      | bool _   => rfl
      | nilV     => trivial
      | sym _    => rfl
      | prim _   => rfl
      | builtinBaseApply => trivial
      | cons x y =>
          obtain ⟨hx, hy⟩ := hv
          exact ⟨ih x h_a extras hh hx, ih y h_a extras hh hy⟩
      | closure ps body cenv =>
          refine ⟨rfl, rfl, ?_⟩
          apply EnvVis_aux_self_of_valid' k cenv h_a (h_a ++ extras) hv hh
              ⟨extras, rfl⟩
          intro v' hv_valid
          exact ih v' h_a extras hh hv_valid

/-! ## Framing theorem (joint mutual statement)

    The headline statement: each function in the four-way mutual
    block preserves bisimulation under state extension and env
    visibility. Mutually proved by induction on fuel; the proof
    structure mirrors `fuel_mono_succ` (when that lemma is added),
    with the additional invariant that `ValVis`/`EnvVis` are
    threaded through inner calls.

    State and prove incrementally — leaf cases are clean; recursive
    cases follow the `rw [F.eq_def]; simp only; cases ...; ih ...`
    template.
-/

private def FrameStmt (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (exp : Expr) (env_a env_b metaEnv : Env)
     (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    StateExt s_a s_b →
    EnvVis env_a env_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    eval n ptable exp env_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      eval n ptable exp env_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      StateExt s_a' s_b') ∧
  (∀ (ptable : PolicyTable) (exps : List Expr) (env_a env_b metaEnv : Env)
     (s_a s_b : RunState) (rs_a : List Val) (s_a' : RunState),
    StateExt s_a s_b →
    EnvVis env_a env_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    evalList n ptable exps env_a metaEnv s_a = some (rs_a, s_a') →
    ∃ rs_b s_b',
      evalList n ptable exps env_b metaEnv s_b = some (rs_b, s_b') ∧
      rs_a.length = rs_b.length ∧
      StateExt s_a' s_b') ∧
  (∀ (ptable : PolicyTable) (op_a op_b : Val) (args_a args_b : List Val)
     (metaEnv : Env) (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    StateExt s_a s_b →
    ValVis op_a op_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    applyVia n ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      applyVia n ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      StateExt s_a' s_b') ∧
  (∀ (ptable : PolicyTable) (op_a op_b : Val) (args_a args_b : List Val)
     (metaEnv : Env) (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    StateExt s_a s_b →
    ValVis op_a op_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    applyDirect n ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      applyDirect n ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      StateExt s_a' s_b')

/-- The main framing theorem. Joint statement, mutually proved by
    induction on fuel. **Stage 3 work item**: the substantive cases
    require state-extension preservation lemmas for `ValVis_aux` and
    `EnvVis_aux` plus careful threading of invariants. The leaf
    cases (literals, vars) are straightforward. -/
theorem frame : ∀ n, FrameStmt n := by
  sorry

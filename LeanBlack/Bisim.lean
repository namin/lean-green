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
      ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
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

/-- The closure case of `ValVis_aux`: bisim-related closures have
    structurally-equal captured envs (`cenv_a = cenv_b`) and the
    captured env's slots in the heap pair are pointwise bisim-
    related at depth `n`. The added `cenv_a = cenv_b` field makes
    cross-side cell updates affect the same index on both sides,
    which is what closes the `.set`-framing case. -/
theorem ValVis_aux_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVis_aux (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
       EnvVis_aux n cenv_a cenv_b h_a h_b) := by
  simp [ValVis_aux, EnvVis_aux]

/-! ## State extension -/

/-- Cross-side state relation: same policy. The heap relation between
    `s_a` and `s_b` is *not* a prefix relation in general (independent
    allocations on the two sides break that), and is instead tracked
    point-wise via `ValVis` / `EnvVis` on the relevant values. -/
def StateExt (s_a s_b : RunState) : Prop :=
  s_a.policy = s_b.policy

theorem StateExt.refl (s : RunState) : StateExt s s := rfl

theorem StateExt.trans {s_a s_b s_c : RunState}
    (h_ab : StateExt s_a s_b) (h_bc : StateExt s_b s_c) :
    StateExt s_a s_c := Eq.trans h_ab h_bc

/-- **Heap-only extension** between states, ignoring the policy. The
    same-side state evolution under `eval`: heap grows monotonically,
    but the policy may change (via `installPolicy`). Distinct from
    `StateExt` (which is *cross-side* and requires same policy on
    both sides). -/
def HeapExt (s_a s_b : RunState) : Prop :=
  ∃ extras, s_b.heap = s_a.heap ++ extras

theorem HeapExt.refl (s : RunState) : HeapExt s s :=
  ⟨[], (List.append_nil _).symm⟩

theorem HeapExt.trans {s_a s_b s_c : RunState}
    (h_ab : HeapExt s_a s_b) (h_bc : HeapExt s_b s_c) :
    HeapExt s_a s_c := by
  obtain ⟨extras_ab, h_heap_ab⟩ := h_ab
  obtain ⟨extras_bc, h_heap_bc⟩ := h_bc
  exact ⟨extras_ab ++ extras_bc, by rw [h_heap_bc, h_heap_ab, List.append_assoc]⟩

theorem HeapExt.heap_le {s_a s_b : RunState} (h : HeapExt s_a s_b) :
    s_a.heap.length ≤ s_b.heap.length := by
  obtain ⟨extras, hext⟩ := h
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

/-! ## `Heap.update` structural lemmas -/

theorem Heap.update_length : ∀ (h : Heap) (idx : Nat) (v : Val),
    (Heap.update h idx v).length = h.length
  | [],       _,     _ => rfl
  | _ :: _,   0,     _ => rfl
  | _ :: t,   n + 1, v => by
      simp only [Heap.update, List.length_cons]
      exact congrArg Nat.succ (Heap.update_length t n v)

/-- Lookup at the updated index returns the new value (provided
    the index is in bounds). -/
theorem Heap.update_get_eq : ∀ (h : Heap) (idx : Nat) (v : Val),
    idx < h.length → (Heap.update h idx v)[idx]? = some v
  | [],       _,     _, h_lt => by simp at h_lt
  | _ :: _,   0,     _, _    => rfl
  | _ :: t,   n + 1, v, h_lt => by
      simp only [Heap.update, List.getElem?_cons_succ]
      have : n < t.length := by
        simp only [List.length_cons] at h_lt
        omega
      exact Heap.update_get_eq t n v this

/-- Lookup at any index ≠ idx is unchanged by the update. -/
theorem Heap.update_get_neq : ∀ (h : Heap) (idx : Nat) (v : Val) (i : Nat),
    i ≠ idx → (Heap.update h idx v)[i]? = h[i]?
  | [],       _,     _, _, _    => rfl
  | _ :: _,   0,     _, 0, hne  => absurd rfl hne
  | _ :: _,   0,     _, _ + 1, _ => rfl
  | _ :: t,   n + 1, v, 0, _    => rfl
  | _ :: t,   n + 1, v, i + 1, hne => by
      simp only [Heap.update, List.getElem?_cons_succ]
      have : i ≠ n := fun h_eq => hne (congrArg Nat.succ h_eq)
      exact Heap.update_get_neq t n v i this

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
          refine ⟨rfl, rfl, rfl, ?_⟩
          apply EnvVis_aux_self_of_valid' k cenv h_a (h_a ++ extras) hv hh
              ⟨extras, rfl⟩
          intro v' hv_valid
          exact ih v' h_a extras hh hv_valid

/-! ## Closed values: heap-independent self-bisimulation

    A `closedValB`-true value contains no closure references, so it
    `ValValid`s in any heap and bisimulates itself across any pair
    of heaps. This is what justifies the `.quote v` case in `frame`:
    `eval` only admits `.quote v` when `closedValB v = true`, so the
    quoted value relates trivially to itself. -/

theorem closedValB_ValValid : ∀ (v : Val) (h : Heap),
    closedValB v = true → ValValid v h
  | .num _,            _, _ => trivial
  | .bool _,           _, _ => trivial
  | .nilV,             _, _ => trivial
  | .sym _,            _, _ => trivial
  | .prim _,           _, _ => trivial
  | .builtinBaseApply, _, _ => trivial
  | .cons x y,         h, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_ValValid x h hc.1, closedValB_ValValid y h hc.2⟩
  | .closure _ _ _,    _, hc => by simp [closedValB] at hc

theorem closedValB_ValVis_aux : ∀ (n : Nat) (v : Val) (h_a h_b : Heap),
    closedValB v = true → ValVis_aux n v v h_a h_b
  | 0,     _,                   _,   _,   _   => trivial
  | _ + 1, .num _,              _,   _,   _   => rfl
  | _ + 1, .bool _,             _,   _,   _   => rfl
  | _ + 1, .nilV,               _,   _,   _   => trivial
  | _ + 1, .sym _,              _,   _,   _   => rfl
  | _ + 1, .prim _,             _,   _,   _   => rfl
  | _ + 1, .builtinBaseApply,   _,   _,   _   => trivial
  | k + 1, .cons x y,           h_a, h_b, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_ValVis_aux k x h_a h_b hc.1,
             closedValB_ValVis_aux k y h_a h_b hc.2⟩
  | _ + 1, .closure _ _ _,      _,   _,   hc => by simp [closedValB] at hc

/-! ## Heap-extension lemmas

    The key building block for framing: bisimulation between
    `(v_a, v_b)` (or `(env_a, env_b)`) is preserved when both heaps
    grow by appended extras. Validity hypotheses ensure that closure
    cenv references stay in the original heap prefix, so heap
    lookups in the extended heaps give the same `Val`s as before.

    Both proofs go by induction on depth `n`. The closure case at
    depth `n+1` uses `EnvVis_aux_extends` at depth `n`, which uses
    `ValVis_aux_extends` at depth `n` (the IH).

    Stage-3 work item: full proof. For now, the lemmas are stated
    so the framing theorem above can be structured against them,
    making the dependency explicit. -/

mutual

theorem ValVis_aux_extends : ∀ (n : Nat) (v_a v_b : Val)
    (h_a h_b ext_a ext_b : Heap),
    HeapValid h_a → HeapValid h_b →
    ValValid v_a h_a → ValValid v_b h_b →
    ValVis_aux n v_a v_b h_a h_b →
    ValVis_aux n v_a v_b (h_a ++ ext_a) (h_b ++ ext_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, ext_a, ext_b,
      hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨ValVis_aux_extends n x_a x_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.1 hv_b.1 h_vis.1,
       ValVis_aux_extends n y_a y_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.2 hv_b.2 h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, ext_a, ext_b, hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨h_vis.1, h_vis.2.1, h_vis.2.2.1,
       EnvVis_aux_extends n cenv_a cenv_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a hv_b h_vis.2.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: h_vis is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVis_aux_extends (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap),
      HeapValid h_a → HeapValid h_b →
      EnvValid env_a h_a → EnvValid env_b h_b →
      EnvVis_aux n env_a env_b h_a h_b →
      EnvVis_aux n env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b h_vis x
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => simp [hl_a, hl_b]
      | some _ => rw [hl_b] at h_x; simp at h_x
  | some i_a =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => rw [hl_b] at h_x; simp at h_x
      | some i_b =>
          rw [hl_b] at h_x
          simp only at h_x
          have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
          have h_lt_b : i_b < h_b.length := hv_b x i_b hl_b
          have h_eq_a : (h_a ++ ext_a)[i_a]? = h_a[i_a]? :=
            getElem?_prefix h_a ext_a i_a h_lt_a
          have h_eq_b : (h_b ++ ext_b)[i_b]? = h_b[i_b]? :=
            getElem?_prefix h_b ext_b i_b h_lt_b
          -- Goal (after cases): match some i_a, some i_b with ... (in ext heaps)
          simp only [hl_a, hl_b]
          -- Simp reduces the outer match (since both args are some); goal is
          -- now the inner match on heap lookups in extended heaps.
          rw [h_eq_a, h_eq_b]
          cases hp_a : h_a[i_a]? with
          | none => rw [hp_a] at h_x; simp at h_x
          | some v_a =>
              cases hp_b : h_b[i_b]? with
              | none => rw [hp_a, hp_b] at h_x; simp at h_x
              | some v_b =>
                  rw [hp_a, hp_b] at h_x
                  have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                  have hv_vb : ValValid v_b h_b := hh_b i_b v_b hp_b
                  exact ValVis_aux_extends n v_a v_b h_a h_b ext_a ext_b
                    hh_a hh_b hv_va hv_vb h_x

end

/-! ## Bisim preservation under cross-side `Heap.update`

    Bisimulation preserved under symmetric in-place update at index
    `idx` to bisim-related new values. The "symmetric" structure is
    enabled by the strengthened `ValVis_aux` on closures (cenvs are
    structurally equal cross-side, so cell-update lookups land at
    the same index on both sides). -/

mutual

theorem ValVis_aux_update : ∀ (n : Nat) (v_a v_b : Val) (h_a h_b : Heap)
    (idx : Nat) (newVal_a newVal_b : Val),
    HeapValid h_a → HeapValid h_b →
    h_a.length = h_b.length →
    ValValid v_a h_a → ValValid v_b h_b →
    -- new values bisim-related at the updated heap pair, at every depth
    (∀ k, ValVis_aux k newVal_a newVal_b
                       (Heap.update h_a idx newVal_a)
                       (Heap.update h_b idx newVal_b)) →
    ValValid newVal_a (Heap.update h_a idx newVal_a) →
    ValValid newVal_b (Heap.update h_b idx newVal_b) →
    ValVis_aux n v_a v_b h_a h_b →
    ValVis_aux n v_a v_b (Heap.update h_a idx newVal_a)
                          (Heap.update h_b idx newVal_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, idx, newVal_a, newVal_b,
      hh_a, hh_b, hlen, hv_a, hv_b, h_vis_new, hv_new_a, hv_new_b, h_vis =>
      ⟨ValVis_aux_update n x_a x_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.1 hv_b.1 h_vis_new hv_new_a hv_new_b h_vis.1,
       ValVis_aux_update n y_a y_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.2 hv_b.2 h_vis_new hv_new_a hv_new_b h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, idx, newVal_a, newVal_b,
      hh_a, hh_b, hlen, hv_a, hv_b, h_vis_new, hv_new_a, hv_new_b, h_vis =>
      -- ValValid on closure unfolds to EnvValid on cenv. Cenv equality
      -- (`h_vis.2.2.1`) is what feeds `EnvVis_aux_update`'s `env_eq`.
      ⟨h_vis.1, h_vis.2.1, h_vis.2.2.1,
       EnvVis_aux_update n cenv_a cenv_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a hv_b h_vis.2.2.1 h_vis_new hv_new_a hv_new_b h_vis.2.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: `h_vis` is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVis_aux_update (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b : Heap)
      (idx : Nat) (newVal_a newVal_b : Val),
      HeapValid h_a → HeapValid h_b →
      h_a.length = h_b.length →
      EnvValid env_a h_a → EnvValid env_b h_b →
      env_a = env_b →   -- structural equality (lookup_eq gives i_a = i_b)
      (∀ k, ValVis_aux k newVal_a newVal_b
                         (Heap.update h_a idx newVal_a)
                         (Heap.update h_b idx newVal_b)) →
      ValValid newVal_a (Heap.update h_a idx newVal_a) →
      ValValid newVal_b (Heap.update h_b idx newVal_b) →
      EnvVis_aux n env_a env_b h_a h_b →
      EnvVis_aux n env_a env_b (Heap.update h_a idx newVal_a)
                                (Heap.update h_b idx newVal_b) := by
  intro env_a env_b h_a h_b idx newVal_a newVal_b
        hh_a hh_b hlen hv_a hv_b h_env_eq h_vis_new hv_new_a hv_new_b h_vis x
  -- env_a = env_b → lookups give the same index on both sides.
  have h_lookup_eq : env_a.lookup x = env_b.lookup x := by rw [h_env_eq]
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x h_lookup_eq
      have hl_b : env_b.lookup x = none := h_lookup_eq.symm
      simp [hl_a, hl_b]
  | some i_a =>
      rw [hl_a] at h_x h_lookup_eq
      have hl_b : env_b.lookup x = some i_a := h_lookup_eq.symm
      rw [hl_b] at h_x
      simp only at h_x
      simp only [hl_a, hl_b]
      have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
      have h_lt_b : i_a < h_b.length := hv_b x i_a hl_b
      -- Both indices equal i_a; case on whether i_a = idx.
      by_cases h_idx : i_a = idx
      · -- Both lookups give the updated cell → newVal_a, newVal_b.
        subst h_idx
        rw [Heap.update_get_eq h_a i_a newVal_a h_lt_a]
        rw [Heap.update_get_eq h_b i_a newVal_b h_lt_b]
        exact h_vis_new n
      · -- Both lookups give an unchanged cell.
        cases hp_a : h_a[i_a]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hp_a
            omega
        | some v_a =>
            cases hp_b : h_b[i_a]? with
            | none =>
                exfalso
                have := List.getElem?_eq_none_iff.mp hp_b
                omega
            | some v_b =>
                rw [Heap.update_get_neq h_a idx newVal_a i_a h_idx, hp_a]
                rw [Heap.update_get_neq h_b idx newVal_b i_a h_idx, hp_b]
                rw [hp_a, hp_b] at h_x
                have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                have hv_vb : ValValid v_b h_b := hh_b i_a v_b hp_b
                exact ValVis_aux_update n v_a v_b h_a h_b idx
                  newVal_a newVal_b hh_a hh_b hlen hv_va hv_vb
                  h_vis_new hv_new_a hv_new_b h_x

end

/-! ## Heap evolution (cross-side framing across in-place updates) -/

/-- **Heap evolution** (cross-side): a strictly weaker relation than
    `HeapExt s_a s_a' ∧ HeapExt s_b s_b'`. The four-place relation
    `HeapEvolution s_a s_b s_a' s_b'` captures what's preserved across
    a *both-sides* step: heap length grows on each side, *and* any
    cross-side env-bisim that held at the source pair `(s_a, s_b)`
    still holds at the target pair `(s_a', s_b')`.

    This is the right relation for framing across `.set` (which
    performs an in-place `Heap.update` and breaks the prefix
    structure of `HeapExt`). The same-side analog would require old
    and new values at the updated cell to be self-bisim-related,
    which fails for `multnExactPolicy` (admits
    `.builtinBaseApply → multn-closure`, not self-bisim). The
    cross-side formulation works because both sides update with
    bisim-*related* new values (via `policy_respects_bisim`), even
    when same-side old/new aren't related.

    Reflexive, transitive, length-monotone, lifted from
    `HeapExt s_a s_a' ∧ HeapExt s_b s_b'` via `from_heapExt`. -/
structure HeapEvolution (s_a s_b s_a' s_b' : RunState) : Prop where
  len_a : s_a.heap.length ≤ s_a'.heap.length
  len_b : s_b.heap.length ≤ s_b'.heap.length
  /-- For every depth `n` and every pair of envs that are
      structurally equal cross-side and bisim-related at depth `n`
      in the source state pair, the same envs remain bisim-related
      in the target state pair. The `env_a = env_b` precondition is
      satisfied at every framing call site by `WFCtx.env_eq`. -/
  env_preserve : ∀ (n : Nat) (env_a env_b : Env),
    env_a = env_b →
    EnvValid env_a s_a.heap → EnvValid env_b s_b.heap →
    EnvVis_aux n env_a env_b s_a.heap s_b.heap →
    EnvVis_aux n env_a env_b s_a'.heap s_b'.heap
  /-- For every depth `n` and every pair of values that were valid in
      the source state pair and bisim-related at depth `n`, the same
      values remain bisim-related in the target state pair at the
      same depth. Used to lift `ValVis` of operands/funcs across
      inner-step heap evolutions in the `.app` / `.primApp` cases. -/
  val_preserve : ∀ (n : Nat) (v_a v_b : Val),
    ValValid v_a s_a.heap → ValValid v_b s_b.heap →
    ValVis_aux n v_a v_b s_a.heap s_b.heap →
    ValVis_aux n v_a v_b s_a'.heap s_b'.heap

theorem HeapEvolution.refl (s_a s_b : RunState) :
    HeapEvolution s_a s_b s_a s_b :=
  ⟨Nat.le_refl _, Nat.le_refl _,
   fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Lift a single-value bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.valVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') (v_a v_b : Val)
    (hv_a : ValValid v_a s_a.heap) (hv_b : ValValid v_b s_b.heap)
    (h_vis : ValVis v_a v_b s_a.heap s_b.heap) :
    ValVis v_a v_b s_a'.heap s_b'.heap := by
  intro n
  exact h.val_preserve n v_a v_b hv_a hv_b (h_vis n)

/-- Lift an env bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.envVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') (env_a env_b : Env)
    (h_env_eq : env_a = env_b)
    (hv_a : EnvValid env_a s_a.heap) (hv_b : EnvValid env_b s_b.heap)
    (h_vis : EnvVis env_a env_b s_a.heap s_b.heap) :
    EnvVis env_a env_b s_a'.heap s_b'.heap := by
  intro n
  exact h.env_preserve n env_a env_b h_env_eq hv_a hv_b (h_vis n)

/-- Validity is preserved under length-monotone evolution. -/
theorem EnvValid.length_mono {env : Env} {h_a h_b : Heap}
    (hv : EnvValid env h_a) (hlen : h_a.length ≤ h_b.length) :
    EnvValid env h_b := by
  intro x i hl
  exact Nat.lt_of_lt_of_le (hv x i hl) hlen

theorem ValValid.length_mono {h_a h_b : Heap} :
    ∀ (v : Val), ValValid v h_a → h_a.length ≤ h_b.length → ValValid v h_b
  | .num _,            _,  _    => trivial
  | .bool _,           _,  _    => trivial
  | .nilV,             _,  _    => trivial
  | .sym _,            _,  _    => trivial
  | .prim _,           _,  _    => trivial
  | .builtinBaseApply, _,  _    => trivial
  | .cons x y,         hv, hlen =>
      ⟨ValValid.length_mono x hv.1 hlen, ValValid.length_mono y hv.2 hlen⟩
  | .closure _ _ _,    hv, hlen =>
      EnvValid.length_mono hv hlen

/-- Transitivity of `HeapEvolution`. Composes env-preservation across
    intermediate state pairs; needs heap validity of the intermediate
    state pair to lift `EnvValid` for the second `env_preserve` call. -/
theorem HeapEvolution.trans {s_a s_b s_a' s_b' s_a'' s_b'' : RunState}
    (h1 : HeapEvolution s_a s_b s_a' s_b')
    (h2 : HeapEvolution s_a' s_b' s_a'' s_b'') :
    HeapEvolution s_a s_b s_a'' s_b'' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans h1.len_a h2.len_a
  · exact Nat.le_trans h1.len_b h2.len_b
  · intro n env_a env_b h_eq hv_a hv_b h_vis
    have h_vis' : EnvVis_aux n env_a env_b s_a'.heap s_b'.heap :=
      h1.env_preserve n env_a env_b h_eq hv_a hv_b h_vis
    have hv_a' : EnvValid env_a s_a'.heap := hv_a.length_mono h1.len_a
    have hv_b' : EnvValid env_b s_b'.heap := hv_b.length_mono h1.len_b
    exact h2.env_preserve n env_a env_b h_eq hv_a' hv_b' h_vis'
  · intro n v_a v_b hv_a hv_b h_vis
    have h_vis' : ValVis_aux n v_a v_b s_a'.heap s_b'.heap :=
      h1.val_preserve n v_a v_b hv_a hv_b h_vis
    have hv_a' : ValValid v_a s_a'.heap := ValValid.length_mono v_a hv_a h1.len_a
    have hv_b' : ValValid v_b s_b'.heap := ValValid.length_mono v_b hv_b h1.len_b
    exact h2.val_preserve n v_a v_b hv_a' hv_b' h_vis'

/-- Lift a pair of `HeapExt`s to a `HeapEvolution`. Used at allocation
    sites (each side appends extras to its heap; old cells preserved).
    Requires heap validity to invoke `ValVis_aux_extends`/`EnvVis_aux_extends`. -/
theorem HeapEvolution.from_heapExt {s_a s_b s_a' s_b' : RunState}
    (hh_a : HeapValid s_a.heap) (hh_b : HeapValid s_b.heap)
    (he_a : HeapExt s_a s_a') (he_b : HeapExt s_b s_b') :
    HeapEvolution s_a s_b s_a' s_b' := by
  obtain ⟨ext_a, hex_a⟩ := he_a
  obtain ⟨ext_b, hex_b⟩ := he_b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex_a, List.length_append]; exact Nat.le_add_right _ _
  · rw [hex_b, List.length_append]; exact Nat.le_add_right _ _
  · intro n env_a env_b _ hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact EnvVis_aux_extends n env_a env_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis
  · intro n v_a v_b hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact ValVis_aux_extends n v_a v_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis

/-! ## Pointwise list bisimulation

    For framing `applyVia` and `applyDirect` (which take `args : List Val`),
    we need pointwise `ValVis` between the two argument lists. -/

def ListValVis : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVis x y h_a h_b ∧ ListValVis xs ys h_a h_b
  | _,       _,       _,   _   => False

/-- Pointwise list validity: each element is `ValValid` in the heap. -/
def ListValValid : List Val → Heap → Prop
  | [],      _ => True
  | x :: xs, h => ValValid x h ∧ ListValValid xs h

theorem ListValVis.length_eq : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b → xs.length = ys.length
  | [],      [],      _, _, _ => rfl
  | [],      _ :: _,  _, _, h => absurd h (by simp [ListValVis])
  | _ :: _,  [],      _, _, h => absurd h (by simp [ListValVis])
  | _ :: xs, _ :: ys, _, _, ⟨_, h_tail⟩ => by
      simp [List.length_cons, ListValVis.length_eq h_tail]

/-- `ListValValid` lifts across heap extension. -/
theorem ListValValid.heap_extends : ∀ {xs : List Val} {h_a h_b : Heap},
    ListValValid xs h_a → (∃ extras, h_b = h_a ++ extras) →
    ListValValid xs h_b
  | [],      _, _, _,  _    => trivial
  | _ :: _, _, _, hv, hext =>
      ⟨ValValid.heap_extends _ hv.1 hext,
       ListValValid.heap_extends hv.2 hext⟩

theorem ListValValid.length_mono {h_a h_b : Heap} :
    ∀ {xs : List Val}, ListValValid xs h_a → h_a.length ≤ h_b.length →
      ListValValid xs h_b
  | [],     _,  _    => trivial
  | _ :: _, hv, hlen =>
      ⟨ValValid.length_mono _ hv.1 hlen,
       ListValValid.length_mono hv.2 hlen⟩

/-- Lift a list bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.listValVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') :
    ∀ (xs ys : List Val),
      ListValValid xs s_a.heap → ListValValid ys s_b.heap →
      ListValVis xs ys s_a.heap s_b.heap →
      ListValVis xs ys s_a'.heap s_b'.heap
  | [],     [],     _,    _,    _    => trivial
  | [],     _ :: _, _,    _,    h_v  => h_v.elim
  | _ :: _, [],     _,    _,    h_v  => h_v.elim
  | x :: xs, y :: ys, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨h.valVis_preserve x y hv_a.1 hv_b.1 h_head,
       h.listValVis_preserve xs ys hv_a.2 hv_b.2 h_tail⟩

/-! ## Bool false characterization -/

/-- `ValVis` on `.bool false` is two-sided: if either side is
    `.bool false`, so is the other. Used by the `.ifte` framing
    case to argue that both calls take the same branch. -/
theorem ValVis_bool_false_iff (cv_a cv_b : Val) (h_a h_b : Heap)
    (h_vv : ValVis cv_a cv_b h_a h_b) :
    cv_a = .bool false ↔ cv_b = .bool false := by
  constructor
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_b with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux] at h1
    | num _            => simp [ValVis_aux] at h1
    | nilV             => simp [ValVis_aux] at h1
    | cons _ _         => simp [ValVis_aux] at h1
    | sym _            => simp [ValVis_aux] at h1
    | closure _ _ _    => simp [ValVis_aux] at h1
    | prim _           => simp [ValVis_aux] at h1
    | builtinBaseApply => simp [ValVis_aux] at h1
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_a with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux] at h1
    | num _            => simp [ValVis_aux] at h1
    | nilV             => simp [ValVis_aux] at h1
    | cons _ _         => simp [ValVis_aux] at h1
    | sym _            => simp [ValVis_aux] at h1
    | closure _ _ _    => simp [ValVis_aux] at h1
    | prim _           => simp [ValVis_aux] at h1
    | builtinBaseApply => simp [ValVis_aux] at h1

/-! ## Universal-depth heap-extension lemmas -/

/-- `ValVis` (universal over depths) preserved under heap extension. -/
theorem ValVis_extends (v_a v_b : Val) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : ValValid v_a h_a) (hv_b : ValValid v_b h_b)
    (h_vis : ValVis v_a v_b h_a h_b) :
    ValVis v_a v_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact ValVis_aux_extends n v_a v_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

/-- `EnvVis` (universal over depths) preserved under heap extension. -/
theorem EnvVis_extends (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : EnvValid env_a h_a) (hv_b : EnvValid env_b h_b)
    (h_vis : EnvVis env_a env_b h_a h_b) :
    EnvVis env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact EnvVis_aux_extends n env_a env_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

/-- `ListValVis` (universal over depths) preserved under heap extension,
    given pointwise `ValValid` on both sides. -/
theorem ListValVis_extends : ∀ {xs ys : List Val} {h_a h_b ext_a ext_b : Heap},
    HeapValid h_a → HeapValid h_b →
    ListValValid xs h_a → ListValValid ys h_b →
    ListValVis xs ys h_a h_b →
    ListValVis xs ys (h_a ++ ext_a) (h_b ++ ext_b)
  | [],      [],      _, _, _, _, _, _, _, _, _ => trivial
  | [],      _ :: _,  _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  [],      _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, _, _, hh_a, hh_b, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_extends _ _ _ _ _ _ hh_a hh_b hv_a.1 hv_b.1 h_head,
       ListValVis_extends hh_a hh_b hv_a.2 hv_b.2 h_tail⟩

/-! ## `listToVal` and bisimulation -/

/-- A `listToVal`-encoded list of bisimilar values produces bisimilar
    cons-spines at every depth. -/
theorem ValVis_aux_listToVal : ∀ (n : Nat) {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b →
    ValVis_aux n (listToVal xs) (listToVal ys) h_a h_b
  | 0, _, _, _, _, _ => trivial
  | _ + 1, [],      [],      _, _, _ => trivial
  | _ + 1, [],      _ :: _,  _, _, h => h.elim
  | _ + 1, _ :: _,  [],      _, _, h => h.elim
  | n + 1, _ :: _, _ :: _, _, _, ⟨h_head, h_tail⟩ =>
      ⟨h_head n, ValVis_aux_listToVal n h_tail⟩

theorem ValVis_listToVal {xs ys : List Val} {h_a h_b : Heap}
    (h : ListValVis xs ys h_a h_b) :
    ValVis (listToVal xs) (listToVal ys) h_a h_b :=
  fun n => ValVis_aux_listToVal n h

theorem ValValid_listToVal : ∀ {xs : List Val} {h : Heap},
    ListValValid xs h → ValValid (listToVal xs) h
  | [],      _, _ => trivial
  | _ :: _,  _, ⟨hv, htail⟩ => ⟨hv, ValValid_listToVal htail⟩

/-! ## `valToList` and bisimulation -/

/-- If `valToList ol_a = some operands_a` and `ValVis ol_a ol_b`, then
    `valToList ol_b` succeeds with operands pointwise bisimilar to
    `operands_a`. Plus pointwise validity. -/
theorem valToList_bisim : ∀ (operands_a : List Val) (ol_a ol_b : Val) (h_a h_b : Heap),
    valToList ol_a = some operands_a → ValVis ol_a ol_b h_a h_b →
    ValValid ol_a h_a → ValValid ol_b h_b →
    ∃ operands_b, valToList ol_b = some operands_b ∧
      ListValVis operands_a operands_b h_a h_b ∧
      ListValValid operands_a h_a ∧ ListValValid operands_b h_b
  | [], ol_a, ol_b, h_a, h_b, hl_a, h_vv, _, _ => by
      have h_vv1 := h_vv 1
      cases ol_a with
      | nilV =>
          cases ol_b with
          | nilV => exact ⟨[], rfl, trivial, trivial, trivial⟩
          | num _ => simp [ValVis_aux] at h_vv1
          | bool _ => simp [ValVis_aux] at h_vv1
          | sym _ => simp [ValVis_aux] at h_vv1
          | cons _ _ => simp [ValVis_aux] at h_vv1
          | closure _ _ _ => simp [ValVis_aux] at h_vv1
          | prim _ => simp [ValVis_aux] at h_vv1
          | builtinBaseApply => simp [ValVis_aux] at h_vv1
      | cons x rest =>
          simp only [valToList] at hl_a
          cases hr : valToList rest with
          | none => rw [hr] at hl_a; simp at hl_a
          | some _ => rw [hr] at hl_a; simp at hl_a
      | num _ => simp [valToList] at hl_a
      | bool _ => simp [valToList] at hl_a
      | sym _ => simp [valToList] at hl_a
      | closure _ _ _ => simp [valToList] at hl_a
      | prim _ => simp [valToList] at hl_a
      | builtinBaseApply => simp [valToList] at hl_a
  | head :: tail, ol_a, ol_b, h_a, h_b, hl_a, h_vv, hv_a, hv_b => by
      -- ol_a must be (.cons head rest) for some rest with valToList rest = some tail.
      have h_vv1 := h_vv 1
      cases ol_a with
      | cons x rest =>
          simp [valToList] at hl_a
          cases hr : valToList rest with
          | none => rw [hr] at hl_a; simp at hl_a
          | some t =>
              rw [hr] at hl_a
              simp at hl_a
              obtain ⟨hx_eq, ht_eq⟩ := hl_a
              subst hx_eq
              subst ht_eq
              -- ol_b must also be cons.
              cases ol_b with
              | cons x_b rest_b =>
                  -- Get bisims on components (universal-depth).
                  have h_vv_head : ValVis x x_b h_a h_b := by
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact (h_vv d'.succ.succ).1
                  have h_vv_rest : ValVis rest rest_b h_a h_b := by
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact (h_vv d'.succ.succ).2
                  -- ValValid on cons → ValValid on components.
                  have hv_a' : ValValid x h_a ∧ ValValid rest h_a := hv_a
                  have hv_b' : ValValid x_b h_b ∧ ValValid rest_b h_b := hv_b
                  -- Recurse on the tail.
                  obtain ⟨tail_b, hl_b, h_lvv_tail, hv_tail_a, hv_tail_b⟩ :=
                    valToList_bisim t rest rest_b h_a h_b hr h_vv_rest hv_a'.2 hv_b'.2
                  refine ⟨x_b :: tail_b, ?_, ⟨h_vv_head, h_lvv_tail⟩,
                          ⟨hv_a'.1, hv_tail_a⟩, ⟨hv_b'.1, hv_tail_b⟩⟩
                  simp [valToList, hl_b]
              | nilV => simp [ValVis_aux] at h_vv1
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
      | nilV => simp [valToList] at hl_a
      | num _ => simp [valToList] at hl_a
      | bool _ => simp [valToList] at hl_a
      | sym _ => simp [valToList] at hl_a
      | closure _ _ _ => simp [valToList] at hl_a
      | prim _ => simp [valToList] at hl_a
      | builtinBaseApply => simp [valToList] at hl_a
  termination_by operands_a _ _ _ _ => operands_a.length


/-! ## `mulConsList` and bisimulation -/

/-- `mulConsList` produces the same `Option Int` on bisimilar values.
    Recurses on the cons-spine of `v_a`. -/
private theorem mulConsList_bisim : ∀ (v_a v_b : Val) (h_a h_b : Heap),
    ValVis v_a v_b h_a h_b → mulConsList v_a = mulConsList v_b
  | .nilV, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | nilV => rfl
      | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.num n) ys, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b ys_b =>
          have h_vv_x : ValVis (.num n) x_b h_a h_b := fun d => by
            cases d with
            | zero => trivial
            | succ d' => exact (h_vv d'.succ.succ).1
          have h_vv_ys : ValVis ys ys_b h_a h_b := fun d => by
            cases d with
            | zero => trivial
            | succ d' => exact (h_vv d'.succ.succ).2
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | num n' =>
              have : n = n' := by simp [ValVis_aux] at h_x_d1; exact h_x_d1
              subst this
              simp [mulConsList, mulConsList_bisim ys ys_b h_a h_b h_vv_ys]
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .num _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | num _ => simp [mulConsList]
      | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .bool _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | bool _ => simp [mulConsList]
      | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .sym _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | sym _ => simp [mulConsList]
      | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.bool _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.bool _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | bool _ => simp [mulConsList]
          | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons .nilV _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis .nilV x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | nilV => simp [mulConsList]
          | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.sym _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.sym _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | sym _ => simp [mulConsList]
          | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.cons _ _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.cons _ _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | cons _ _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.closure _ _ _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.closure _ _ _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | closure _ _ _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.prim _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.prim _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | prim _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons .builtinBaseApply _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis .builtinBaseApply x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | builtinBaseApply => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .closure _ _ _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | closure _ _ _ => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .prim _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | prim _ => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .builtinBaseApply, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | builtinBaseApply => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
          simp [ValVis_aux] at h_d1

/-! ## `applyPrim` and bisimulation -/

/-- For each "predicate-style" primitive (one-argument constructor check
    returning a Bool), the result depends only on the depth-1 constructor
    of the argument, which is preserved by `ValVis_aux 1`. Bisimilar
    arguments therefore give equal results. We prove the same equality
    fact for all binary-numeric, cons, car, cdr, mul-list primitives.
    For the cons-y prims the equality is in `Option Val` modulo bisim. -/

private theorem applyPrim_numQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_numQ args_a = applyPrim_numQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_boolQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_boolQ args_a = applyPrim_boolQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_closureQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_closureQ args_a = applyPrim_closureQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_primQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_primQ args_a = applyPrim_primQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_nullQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_nullQ args_a = applyPrim_nullQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

/-! ## Binary numeric prims and bisimulation -/

/-- Helper: for ValVis-related lists of length ≠ 2, the binary numeric prim
    helpers (plus, minus, times, eq) all return `none` on both sides. -/
private theorem applyPrim_plus_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_plus args_a = applyPrim_plus args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_plus]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_plus]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_plus]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_plus]

private theorem applyPrim_minus_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_minus args_a = applyPrim_minus args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_minus]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_minus]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_minus]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_minus]

private theorem applyPrim_times_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_times args_a = applyPrim_times args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_times]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_times]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_times]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_times]

private theorem applyPrim_eq_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_eq args_a = applyPrim_eq args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_eq]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_eq]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_eq]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_eq]

/-! ## `mul-list` prim bisim -/

private theorem applyPrim_mulList_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_mulList args_a = applyPrim_mulList args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_mulList]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              -- args = [v]. mulConsList v_a = mulConsList v_b by mulConsList_bisim.
              simp only [applyPrim_mulList]
              rw [mulConsList_bisim v_a v_b h_a h_b h_vv_v]

/-! ## `cons`, `car`, `cdr` prim bisim -/

private theorem applyPrim_cons_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_cons args_a = some r_a) :
    ∃ r_b, applyPrim_cons args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_cons] at h
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v0_a, hv_rest_a⟩ := hv_a
        obtain ⟨hv_v0_b, hv_rest_b⟩ := hv_b
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_cons] at h
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              obtain ⟨hv_v1_a, hv_rest2_a⟩ := hv_rest_a
              obtain ⟨hv_v1_b, hv_rest2_b⟩ := hv_rest_b
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_cons] at h
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    -- args = [v0, v1]. result = .cons v0 v1.
                    simp only [applyPrim_cons, Option.some.injEq] at h
                    subst h
                    refine ⟨.cons v0_b v1_b, by simp [applyPrim_cons], ?_,
                            ⟨hv_v0_a, hv_v1_a⟩, ⟨hv_v0_b, hv_v1_b⟩⟩
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact ⟨h_vv_v0 d', h_vv_v1 d'⟩

private theorem applyPrim_car_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_car args_a = some r_a) :
    ∃ r_b, applyPrim_car args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_car] at h
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v_a, _⟩ := hv_a
        obtain ⟨hv_v_b, _⟩ := hv_b
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_car] at h
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              -- args = [v]. v must be .cons (else applyPrim_car returns none).
              cases v_a with
              | cons xa ya =>
                  -- v_b also .cons (forced by ValVis_aux 1).
                  have h_v_d1 := h_vv_v 1
                  cases v_b with
                  | cons xb yb =>
                      simp only [applyPrim_car, Option.some.injEq] at h
                      subst h
                      have h_vv_xy : ValVis (.cons xa ya) (.cons xb yb) h_a h_b := h_vv_v
                      -- Extract ValVis xa xb.
                      refine ⟨xb, by simp [applyPrim_car], ?_, hv_v_a.1, hv_v_b.1⟩
                      intro d
                      cases d with
                      | zero => trivial
                      | succ d' => exact (h_vv_xy d'.succ.succ).1
                  | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                  | builtinBaseApply => simp [ValVis_aux] at h_v_d1
              | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
              | builtinBaseApply => simp [applyPrim_car] at h

private theorem applyPrim_cdr_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_cdr args_a = some r_a) :
    ∃ r_b, applyPrim_cdr args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_cdr] at h
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v_a, _⟩ := hv_a
        obtain ⟨hv_v_b, _⟩ := hv_b
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_cdr] at h
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              cases v_a with
              | cons xa ya =>
                  have h_v_d1 := h_vv_v 1
                  cases v_b with
                  | cons xb yb =>
                      simp only [applyPrim_cdr, Option.some.injEq] at h
                      subst h
                      have h_vv_xy : ValVis (.cons xa ya) (.cons xb yb) h_a h_b := h_vv_v
                      refine ⟨yb, by simp [applyPrim_cdr], ?_, hv_v_a.2, hv_v_b.2⟩
                      intro d
                      cases d with
                      | zero => trivial
                      | succ d' => exact (h_vv_xy d'.succ.succ).2
                  | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                  | builtinBaseApply => simp [ValVis_aux] at h_v_d1
              | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
              | builtinBaseApply => simp [applyPrim_cdr] at h

/-! ## Result-form facts for each prim helper -/

/-- For each "scalar-result" prim helper, the successful result is always
    one of `.num _` or `.bool _`. We prove this once per prim so that the
    combined `applyPrim_bisim` can derive `ValVis r r` reflexively (which
    is trivial for these scalar types). -/

private theorem applyPrim_plus_some_form {args : List Val} {r : Val}
    (h : applyPrim_plus args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_plus] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_plus] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_plus] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_plus, Option.some.injEq] at h
                exact ⟨a + b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_plus] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_plus] at h

private theorem applyPrim_minus_some_form {args : List Val} {r : Val}
    (h : applyPrim_minus args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_minus] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_minus] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_minus] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_minus, Option.some.injEq] at h
                exact ⟨a - b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_minus] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_minus] at h

private theorem applyPrim_times_some_form {args : List Val} {r : Val}
    (h : applyPrim_times args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_times] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_times] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_times] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_times, Option.some.injEq] at h
                exact ⟨a * b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_times] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_times] at h

private theorem applyPrim_eq_some_form {args : List Val} {r : Val}
    (h : applyPrim_eq args = some r) : ∃ b : Bool, r = .bool b := by
  cases args with
  | nil => simp [applyPrim_eq] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_eq] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_eq] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_eq, Option.some.injEq] at h
                exact ⟨a == b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_eq] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_eq] at h

private theorem applyPrim_mulList_some_form {args : List Val} {r : Val}
    (h : applyPrim_mulList args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_mulList] at h
  | cons v rest => cases rest with
    | cons _ _ => simp [applyPrim_mulList] at h
    | nil =>
        simp only [applyPrim_mulList] at h
        cases hm : mulConsList v with
        | none => rw [hm] at h; simp at h
        | some n =>
            rw [hm] at h
            simp only [Option.map_some, Option.some.injEq] at h
            exact ⟨n, h.symm⟩

/-! ## Combined `applyPrim` bisim -/

theorem applyPrim_bisim (name : String) (args_a args_b : List Val) (h_a h_b : Heap)
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim name args_a = some r_a) :
    ∃ r_b, applyPrim name args_b = some r_b ∧
           ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  -- Helper: ValVis (.num n) (.num n) for any heaps.
  have valVis_num : ∀ (n : Int), ValVis (.num n) (.num n) h_a h_b := fun n d => by
    cases d with | zero => trivial | succ _ => rfl
  -- Helper: ValVis (.bool b) (.bool b) for any heaps.
  have valVis_bool : ∀ (b : Bool), ValVis (.bool b) (.bool b) h_a h_b := fun b d => by
    cases d with | zero => trivial | succ _ => rfl
  -- For each prim where the result is `.num _` or `.bool _`, the equality
  -- lemma + result-form lemma combine to give the bisim. For cons/car/cdr,
  -- use the dedicated bisim helpers.
  unfold applyPrim at h ⊢
  by_cases hp_plus : name = "+"
  · subst hp_plus
    simp only [↓reduceIte] at h ⊢
    have heq := applyPrim_plus_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_plus_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_minus : name = "-"
  · subst hp_minus
    simp only [↓reduceIte, hp_plus] at h ⊢
    have heq := applyPrim_minus_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_minus_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_times : name = "*"
  · subst hp_times
    simp only [↓reduceIte, hp_plus, hp_minus] at h ⊢
    have heq := applyPrim_times_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_times_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_mul : name = "mul-list"
  · subst hp_mul
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times] at h ⊢
    have heq := applyPrim_mulList_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_mulList_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_eq : name = "="
  · subst hp_eq
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul] at h ⊢
    have heq := applyPrim_eq_eq h_lvv
    obtain ⟨b, rfl⟩ := applyPrim_eq_some_form h
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  -- Predicate prims (numQ, boolQ, closureQ, primQ, nullQ): all return .bool.
  -- The equality lemma + result-form give bisim. For these we use a direct
  -- helper-pair: equality lemma + a small `applyPrim_X_some_form` showing
  -- result is `.bool _`. We inline the form proofs since they're tiny.
  by_cases hp_numQ : name = "num?"
  · subst hp_numQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq] at h ⊢
    have heq := applyPrim_numQ_bisim h_lvv
    -- result of applyPrim_numQ is always .bool (or none).
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_numQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_numQ] at h
          | nil =>
              cases v with
              | num _ =>
                  simp only [applyPrim_numQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_numQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_boolQ : name = "bool?"
  · subst hp_boolQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ] at h ⊢
    have heq := applyPrim_boolQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_boolQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_boolQ] at h
          | nil =>
              cases v with
              | bool _ =>
                  simp only [applyPrim_boolQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_boolQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_closureQ : name = "closure?"
  · subst hp_closureQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ] at h ⊢
    have heq := applyPrim_closureQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_closureQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_closureQ] at h
          | nil =>
              cases v with
              | closure _ _ _ =>
                  simp only [applyPrim_closureQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_closureQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_primQ : name = "prim?"
  · subst hp_primQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ] at h ⊢
    have heq := applyPrim_primQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_primQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_primQ] at h
          | nil =>
              cases v with
              | prim _ =>
                  simp only [applyPrim_primQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
              | builtinBaseApply =>
                  simp only [applyPrim_primQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_cons : name = "cons"
  · subst hp_cons
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ] at h ⊢
    exact applyPrim_cons_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_car : name = "car"
  · subst hp_car
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons] at h ⊢
    exact applyPrim_car_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_cdr : name = "cdr"
  · subst hp_cdr
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons, hp_car] at h ⊢
    exact applyPrim_cdr_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_nullQ : name = "null?"
  · subst hp_nullQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons, hp_car, hp_cdr] at h ⊢
    have heq := applyPrim_nullQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_nullQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_nullQ] at h
          | nil =>
              cases v with
              | nilV =>
                  simp only [applyPrim_nullQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_nullQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  -- Unknown name: applyPrim returns none.
  exfalso
  simp only [hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ, hp_boolQ,
             hp_closureQ, hp_primQ, hp_cons, hp_car, hp_cdr, hp_nullQ,
             ↓reduceIte] at h
  exact Option.noConfusion h

/-! ## Cons-extension of `EnvVis` -/

/-- Adding a fresh `(x, idx_a)` / `(x, idx_b)` binding on top of related
    envs preserves `EnvVis_aux` provided the pointed-to values are
    `ValVis_aux`-related at the same depth. -/
theorem EnvVis_aux_cons (d : Nat) (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVis_aux d v_a v_b h_a h_b)
    (h_env : EnvVis_aux d env_a env_b h_a h_b) :
    EnvVis_aux d (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro name
  simp only [Env.lookup]
  by_cases h_eq : x = name
  · subst h_eq
    simp only [beq_self_eq_true, ↓reduceIte, h_lookup_a, h_lookup_b]
    exact h_vv
  · have h_neq : (x == name) = false := by
      rw [beq_eq_false_iff_ne]; exact h_eq
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte]
    exact h_env name

/-- Universal-depth version. -/
theorem EnvVis_cons (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVis v_a v_b h_a h_b)
    (h_env : EnvVis env_a env_b h_a h_b) :
    EnvVis (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro d
  exact EnvVis_aux_cons d x idx_a idx_b env_a env_b h_a h_b v_a v_b
    h_lookup_a h_lookup_b (h_vv d) (h_env d)

/-! ## Closure-call alloc-chain invariant -/

/-- The body of the closure-call foldl in `applyDirect`. -/
def allocStep (acc : Heap × Env) (vp : Val × String) : Heap × Env :=
  let (hh, ee) := acc
  let (hh', idx) := hh.alloc vp.1
  (hh', .cons vp.2 idx ee)

/-- Cross-side alignment of `allocStep` chains: starting from
    accumulators with equal env and equal-length heap, after `foldl`-
    ing the same parameter list with two same-length value lists, the
    output envs match and the output heap lengths match. The values
    in the heap may differ; only structure is preserved. -/
theorem allocStep_chain_aligned :
    ∀ (xs_a xs_b : List Val) (ps : List String)
      (h_a h_b : Heap) (cenv : Env),
      h_a.length = h_b.length →
      xs_a.length = xs_b.length →
      ((xs_a.zip ps).foldl allocStep (h_a, cenv)).2 =
        ((xs_b.zip ps).foldl allocStep (h_b, cenv)).2 ∧
      ((xs_a.zip ps).foldl allocStep (h_a, cenv)).1.length =
        ((xs_b.zip ps).foldl allocStep (h_b, cenv)).1.length
  | [], [], _, _, _, _, h_len, _ => by
      simp [List.zip_nil_left, List.foldl, h_len]
  | [], _ :: _, _, _, _, _, _, h_args => by simp at h_args
  | _ :: _, [], _, _, _, _, _, h_args => by simp at h_args
  | _ :: xs_a, _ :: xs_b, [], _, _, _, h_len, _ => by
      simp [List.zip_nil_right, List.foldl, h_len]
  | x_a :: xs_a, x_b :: xs_b, p :: ps, h_a, h_b, cenv, h_len, h_args => by
      simp only [List.zip_cons_cons, List.foldl_cons, allocStep, Heap.alloc]
      have h_args' : xs_a.length = xs_b.length := by simp at h_args; exact h_args
      have h_len' : (h_a ++ [x_a]).length = (h_b ++ [x_b]).length := by
        simp [List.length_append, h_len]
      have h_cenv_eq :
          (Env.cons p h_a.length cenv) = (Env.cons p h_b.length cenv) := by
        rw [h_len]
      rw [h_cenv_eq]
      exact allocStep_chain_aligned xs_a xs_b ps (h_a ++ [x_a]) (h_b ++ [x_b])
        (Env.cons p h_b.length cenv) h_len' h_args'

/-! ## Self-extend helpers -/

/-- A list of `ValValid` values is `ListValVis` with itself across a
    heap extension. Used to build self-bisim hypotheses for the
    inner `frame.applyDirect` call in `multnExact_CE_nonnum_case`. -/
theorem ListValVis_self_extend : ∀ {xs : List Val} {h : Heap} (extras : Heap),
    HeapValid h → ListValValid xs h →
    ListValVis xs xs h (h ++ extras)
  | [], _, _, _, _ => trivial
  | x :: _, h, extras, hh, ⟨hv_x, hv_rest⟩ =>
      ⟨fun d => ValVis_aux_self_extend d x h extras hh hv_x,
       ListValVis_self_extend extras hh hv_rest⟩

/-! ## Env-lookup helpers for the multn closure-body trace -/

theorem env_alloc_lookup_op (s_heap : Heap) (cenv : Env) :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup "op" = some s_heap.length := by
  simp [Env.lookup]

theorem env_alloc_lookup_args (s_heap : Heap) (cenv : Env) :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup "args" = some (s_heap.length + 1) := by
  simp [Env.lookup]

theorem env_alloc_lookup_other {s_heap : Heap} {cenv : Env}
    (x : String) (h1 : x ≠ "args") (h2 : x ≠ "op") :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup x = cenv.lookup x := by
  simp [Env.lookup, h1.symm, h2.symm]

/-- Foldl-allocation preserves the validity and bisimulation invariants:
    starting from `EnvVis`-related cenvs and pointwise-bisim args, the
    resulting (extended-heap, cons-extended-env) pairs satisfy `WFCtx`-shape
    invariants and `EnvVis` on the extended envs. Used by `applyDirect`'s
    closure case in the framing theorem. -/
private theorem alloc_chain_bisim
    (xs_a : List Val) :
    ∀ (xs_b : List Val) (ps : List String) (cenv_a cenv_b : Env) (h_a h_b : Heap),
    xs_a.length = ps.length → xs_b.length = ps.length →
    ListValVis xs_a xs_b h_a h_b →
    ListValValid xs_a h_a → ListValValid xs_b h_b →
    HeapValid h_a → HeapValid h_b →
    EnvValid cenv_a h_a → EnvValid cenv_b h_b →
    EnvVis cenv_a cenv_b h_a h_b →
    let result_a := xs_a.zip ps |>.foldl allocStep (h_a, cenv_a)
    let result_b := xs_b.zip ps |>.foldl allocStep (h_b, cenv_b)
    HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
    EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
    EnvVis result_a.2 result_b.2 result_a.1 result_b.1 ∧
    (∃ ext, result_a.1 = h_a ++ ext) ∧
    (∃ ext, result_b.1 = h_b ++ ext) := by
  induction xs_a with
  | nil =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      simp only [List.length_nil] at hlen_a
      have hps_nil : ps = [] := List.length_eq_zero_iff.mp hlen_a.symm
      subst hps_nil
      simp only [List.length_nil] at hlen_b
      have hxs_b_nil : xs_b = [] := List.length_eq_zero_iff.mp hlen_b
      subst hxs_b_nil
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hh_a
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hh_b
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                     (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hev_a
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                     (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hev_b
      · show EnvVis (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                    (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                    (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
                    (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact h_env
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
          = h_a ++ ext
        simp [List.foldl]
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
          = h_b ++ ext
        simp [List.foldl]
  | cons a_a rest_a ih =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      cases ps with
      | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at hlen_a
          omega
      | cons p rest_p =>
          cases xs_b with
          | nil =>
              exfalso
              simp only [List.length_nil, List.length_cons] at hlen_b
              omega
          | cons a_b rest_b =>
              simp only [List.length_cons] at hlen_a hlen_b
              have hlen_a' : rest_a.length = rest_p.length := by omega
              have hlen_b' : rest_b.length = rest_p.length := by omega
              obtain ⟨h_vv_a, h_lvv_rest⟩ := h_lvv
              obtain ⟨hv_a_a, hv_rest_a⟩ := hv_xs_a
              obtain ⟨hv_a_b, hv_rest_b⟩ := hv_xs_b
              -- After one foldl step on each side.
              show
                let result_a := rest_a.zip rest_p |>.foldl allocStep
                  (h_a ++ [a_a], .cons p h_a.length cenv_a)
                let result_b := rest_b.zip rest_p |>.foldl allocStep
                  (h_b ++ [a_b], .cons p h_b.length cenv_b)
                HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
                EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
                EnvVis result_a.2 result_b.2 result_a.1 result_b.1 ∧
                (∃ ext, result_a.1 = h_a ++ ext) ∧
                (∃ ext, result_b.1 = h_b ++ ext)
              -- Establish invariants for the new (h, env) pair.
              have hh_a' : HeapValid (h_a ++ [a_a]) := by
                intro i v hp
                by_cases h_lt : i < h_a.length
                · have hp_old : h_a[i]? = some v := by
                    rw [← getElem?_prefix h_a [a_a] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_a i v hp_old) ⟨[a_a], rfl⟩
                · have h_eq : i = h_a.length := by
                    have h_le : i < (h_a ++ [a_a]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_a hv_a_a ⟨[a_a], rfl⟩
              have hh_b' : HeapValid (h_b ++ [a_b]) := by
                intro i v hp
                by_cases h_lt : i < h_b.length
                · have hp_old : h_b[i]? = some v := by
                    rw [← getElem?_prefix h_b [a_b] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_b i v hp_old) ⟨[a_b], rfl⟩
                · have h_eq : i = h_b.length := by
                    have h_le : i < (h_b ++ [a_b]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_b hv_a_b ⟨[a_b], rfl⟩
              have hev_a' : EnvValid (.cons p h_a.length cenv_a) (h_a ++ [a_a]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_a name i hl
                  omega
              have hev_b' : EnvValid (.cons p h_b.length cenv_b) (h_b ++ [a_b]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_b name i hl
                  omega
              -- Lookups at the fresh indices.
              have hl_a : (h_a ++ [a_a])[h_a.length]? = some a_a := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              have hl_b : (h_b ++ [a_b])[h_b.length]? = some a_b := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              -- ValVis a_a a_b lifted to extended heaps.
              have h_vv_a' : ValVis a_a a_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ValVis_extends a_a a_b h_a h_b [a_a] [a_b] hh_a hh_b hv_a_a hv_a_b h_vv_a
              -- EnvVis cenv_a cenv_b lifted.
              have h_env_lifted : EnvVis cenv_a cenv_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVis_extends cenv_a cenv_b h_a h_b [a_a] [a_b]
                  hh_a hh_b hev_a hev_b h_env
              -- EnvVis on the new cons-extended env.
              have h_env' : EnvVis (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVis_cons p h_a.length h_b.length cenv_a cenv_b
                  (h_a ++ [a_a]) (h_b ++ [a_b]) a_a a_b hl_a hl_b h_vv_a' h_env_lifted
              -- Lift ListValVis rest_a rest_b to extended heaps.
              have h_lvv_rest' : ListValVis rest_a rest_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ListValVis_extends hh_a hh_b hv_rest_a hv_rest_b h_lvv_rest
              -- Lift validity of rest_a / rest_b.
              have hv_rest_a' : ListValValid rest_a (h_a ++ [a_a]) :=
                ListValValid.heap_extends hv_rest_a ⟨[a_a], rfl⟩
              have hv_rest_b' : ListValValid rest_b (h_b ++ [a_b]) :=
                ListValValid.heap_extends hv_rest_b ⟨[a_b], rfl⟩
              -- Apply IH on rest.
              obtain ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
                ih rest_b rest_p (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b])
                  hlen_a' hlen_b' h_lvv_rest' hv_rest_a' hv_rest_b'
                  hh_a' hh_b' hev_a' hev_b' h_env'
              refine ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ?_, ?_⟩
              · exact ⟨[a_a] ++ ext_a, by rw [hex_a, List.append_assoc]⟩
              · exact ⟨[a_b] ++ ext_b, by rw [hex_b, List.append_assoc]⟩

/-! ## ValVis on closures → EnvVis on cenvs -/

/-- The closure case of `ValVis_aux (n+1)` is exactly `EnvVis_aux n` on the
    captured envs (plus body/params/cenv-structural equality). Lifting
    to all depths gives `EnvVis cenv_a cenv_b`. -/
theorem closure_ValVis_imp_cenv_EnvVis
    {ps_a ps_b : List String} {body_a body_b : Expr} {cenv_a cenv_b : Env}
    {h_a h_b : Heap}
    (h_vv : ValVis (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b) :
    ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
    EnvVis cenv_a cenv_b h_a h_b := by
  have h1 := h_vv 1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
  intro d
  exact (h_vv (d + 1)).2.2.2

/-! ## Framing theorem (joint mutual statement)

    Each function in the four-way mutual block preserves bisimulation
    under state extension and env visibility. Mutually proved by
    induction on fuel; same template as `fuel_mono_succ`-style proofs,
    with `ValVis`/`EnvVis` invariants threaded through inner calls.

    The framing theorem requires `WFCtx` (well-formed runtime
    context: state extension + heap and env validity) as a hypothesis
    and produces it for the result state. Without these, the
    recursive cases cannot use `EnvVis_aux_extends` to propagate
    `EnvVis` through inner allocs.
-/

/-- A policy **respects bisim**: cross-side, the policy gives the
    same admit/reject decision on bisim-related arguments evaluated
    in bisim-related heaps. This is the property that makes the
    framing theorem's `.set` case go through.

    The policy can inspect the heap, env, metaEnv via `MutationCtx`,
    so we require it to agree under bisim of those components (env
    and metaEnv are the *same* on both sides — they're identifier-
    to-index maps that the runtime uses on both sides identically;
    heaps differ but are `EnvVis`-related).
    -/
def PolicyRespectsBisim (p : BlackPolicy) : Prop :=
  ∀ (target : String) (idx : Nat) (env metaEnv : Env)
    (heap_a heap_b : Heap) (oldVal_a oldVal_b new_a new_b : Val),
    HeapValid heap_a → HeapValid heap_b →
    EnvValid env heap_a → EnvValid env heap_b →
    EnvValid metaEnv heap_a → EnvValid metaEnv heap_b →
    ValValid oldVal_a heap_a → ValValid oldVal_b heap_b →
    ValValid new_a heap_a → ValValid new_b heap_b →
    EnvVis env env heap_a heap_b →
    EnvVis metaEnv metaEnv heap_a heap_b →
    ValVis oldVal_a oldVal_b heap_a heap_b →
    ValVis new_a new_b heap_a heap_b →
    p { target := target, heap := heap_a, env := env,
        metaEnv := metaEnv, index := idx } oldVal_a new_a =
    p { target := target, heap := heap_b, env := env,
        metaEnv := metaEnv, index := idx } oldVal_b new_b

/-- A policy table where every entry respects bisim. -/
def PolicyTableRespectsBisim (ptable : PolicyTable) : Prop :=
  ∀ (idx : Nat) p, ptable[idx]? = some p → PolicyRespectsBisim p

/-- Well-formed runtime context for the bisimulation: state pairs
    related by `StateExt`, heaps `HeapValid`, envs `EnvValid` in
    their respective heaps, the active policy respects bisim, and
    cross-side structural alignment of envs and heap lengths. The
    `env_eq` and `heap_len_eq` fields are *new* invariants needed to
    close the `.set` case: they ensure `env.lookup x` produces the
    same `idx` cross-side (so `isMetaMutation` and the heap update
    target the same cell on both sides), and that `.letE` and
    closure-call alloc indices match cross-side. The runner
    establishes both invariants initially, and every framing step
    preserves them. -/
structure WFCtx (env_a env_b metaEnv : Env) (s_a s_b : RunState) : Prop where
  state_ext : StateExt s_a s_b
  hv_a      : HeapValid s_a.heap
  hv_b      : HeapValid s_b.heap
  ev_a      : EnvValid env_a s_a.heap
  ev_b      : EnvValid env_b s_b.heap
  em_a      : EnvValid metaEnv s_a.heap
  em_b      : EnvValid metaEnv s_b.heap
  policy_resp : PolicyRespectsBisim s_a.policy
  env_eq      : env_a = env_b
  heap_len_eq : s_a.heap.length = s_b.heap.length

theorem WFCtx.refl (env metaEnv : Env) (s : RunState)
    (hh : HeapValid s.heap) (hev : EnvValid env s.heap)
    (hem : EnvValid metaEnv s.heap)
    (hresp : PolicyRespectsBisim s.policy) :
    WFCtx env env metaEnv s s :=
  ⟨StateExt.refl s, hh, hh, hev, hev, hem, hem, hresp, rfl, rfl⟩

private def FrameStmt (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (exp : Expr) (env_a env_b metaEnv : Env)
     (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    PolicyTableRespectsBisim ptable →
    WFCtx env_a env_b metaEnv s_a s_b →
    EnvVis env_a env_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    eval n ptable exp env_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      eval n ptable exp env_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      WFCtx env_a env_b metaEnv s_a' s_b' ∧
      HeapEvolution s_a s_b s_a' s_b' ∧
      EnvVis env_a env_b s_a'.heap s_b'.heap ∧
      EnvVis metaEnv metaEnv s_a'.heap s_b'.heap ∧
      ValValid r_a s_a'.heap ∧ ValValid r_b s_b'.heap) ∧
  (∀ (ptable : PolicyTable) (exps : List Expr) (env_a env_b metaEnv : Env)
     (s_a s_b : RunState) (rs_a : List Val) (s_a' : RunState),
    PolicyTableRespectsBisim ptable →
    WFCtx env_a env_b metaEnv s_a s_b →
    EnvVis env_a env_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    evalList n ptable exps env_a metaEnv s_a = some (rs_a, s_a') →
    ∃ rs_b s_b',
      evalList n ptable exps env_b metaEnv s_b = some (rs_b, s_b') ∧
      ListValVis rs_a rs_b s_a'.heap s_b'.heap ∧
      WFCtx env_a env_b metaEnv s_a' s_b' ∧
      HeapEvolution s_a s_b s_a' s_b' ∧
      EnvVis env_a env_b s_a'.heap s_b'.heap ∧
      EnvVis metaEnv metaEnv s_a'.heap s_b'.heap ∧
      ListValValid rs_a s_a'.heap ∧ ListValValid rs_b s_b'.heap) ∧
  (∀ (ptable : PolicyTable) (op_a op_b : Val) (args_a args_b : List Val)
     (metaEnv : Env) (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    PolicyTableRespectsBisim ptable →
    WFCtx metaEnv metaEnv metaEnv s_a s_b →
    ValVis op_a op_b s_a.heap s_b.heap →
    ListValVis args_a args_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    ValValid op_a s_a.heap → ValValid op_b s_b.heap →
    ListValValid args_a s_a.heap → ListValValid args_b s_b.heap →
    applyVia n ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      applyVia n ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      WFCtx metaEnv metaEnv metaEnv s_a' s_b' ∧
      HeapEvolution s_a s_b s_a' s_b' ∧
      EnvVis metaEnv metaEnv s_a'.heap s_b'.heap ∧
      ValValid r_a s_a'.heap ∧ ValValid r_b s_b'.heap) ∧
  (∀ (ptable : PolicyTable) (op_a op_b : Val) (args_a args_b : List Val)
     (metaEnv : Env) (s_a s_b : RunState) (r_a : Val) (s_a' : RunState),
    PolicyTableRespectsBisim ptable →
    WFCtx metaEnv metaEnv metaEnv s_a s_b →
    ValVis op_a op_b s_a.heap s_b.heap →
    ListValVis args_a args_b s_a.heap s_b.heap →
    EnvVis metaEnv metaEnv s_a.heap s_b.heap →
    ValValid op_a s_a.heap → ValValid op_b s_b.heap →
    ListValValid args_a s_a.heap → ListValValid args_b s_b.heap →
    applyDirect n ptable op_a args_a metaEnv s_a = some (r_a, s_a') →
    ∃ r_b s_b',
      applyDirect n ptable op_b args_b metaEnv s_b = some (r_b, s_b') ∧
      ValVis r_a r_b s_a'.heap s_b'.heap ∧
      WFCtx metaEnv metaEnv metaEnv s_a' s_b' ∧
      HeapEvolution s_a s_b s_a' s_b' ∧
      EnvVis metaEnv metaEnv s_a'.heap s_b'.heap ∧
      ValValid r_a s_a'.heap ∧ ValValid r_b s_b'.heap)

/-- The main framing theorem. Joint statement, mutually proved by
    induction on fuel.

    Status: zero case + eval's leaf cases (literals, var, lam,
    installPolicy) proved here. Recursive cases (.ifte, .app,
    .primApp, .set, .em, .letE, .seq) and the other three function
    cases (evalList, applyVia, applyDirect) follow the same template
    that closed `fuel_mono_succ` in lean-grey, threading `ValVis` /
    `EnvVis` invariants through inner calls. ~400 LOC remaining. -/
theorem frame : ∀ n, FrameStmt n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [eval] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable exp env_a env_b metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_env h_meta h_eval
        have h_state := h_ctx.state_ext
        cases exp with
        | num i =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            refine ⟨.num i, s_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, h_meta, trivial, trivial⟩
            · simp [eval]
            · intro depth
              cases depth with | zero => trivial | succ _ => rfl
        | bool b =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            refine ⟨.bool b, s_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, h_meta, trivial, trivial⟩
            · simp [eval]
            · intro depth
              cases depth with | zero => trivial | succ _ => rfl
        | quote v =>
            -- `eval` only admits `.quote v` when `closedValB v = true`;
            -- closed values self-bisimulate across any heap pair, so the
            -- case closes via `closedValB_ValVis_aux` and `closedValB_ValValid`.
            simp only [eval] at h_eval
            split at h_eval
            · rename_i h_closed
              simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨h_r, h_s⟩ := h_eval
              subst h_r; subst h_s
              refine ⟨v, s_b, ?_, ?_, h_ctx,
                      HeapEvolution.refl _ _, h_env, h_meta,
                      closedValB_ValValid v s_a.heap h_closed,
                      closedValB_ValValid v s_b.heap h_closed⟩
              · simp [eval, h_closed]
              · intro depth
                exact closedValB_ValVis_aux depth v s_a.heap s_b.heap h_closed
            · simp at h_eval
        | var x =>
            simp only [eval] at h_eval
            cases hl_a : env_a.lookup x with
            | none => rw [hl_a] at h_eval; simp at h_eval
            | some i_a =>
                rw [hl_a] at h_eval
                simp only at h_eval
                cases hp_a : s_a.heap[i_a]? with
                | none => rw [hp_a] at h_eval; simp at h_eval
                | some v_a =>
                    rw [hp_a] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_r, h_s⟩ := h_eval
                    subst h_r; subst h_s
                    -- Extract i_b and v_b from EnvVis_aux at depth 1.
                    have h_x1 := h_env 1 x
                    rw [hl_a] at h_x1
                    cases hl_b : env_b.lookup x with
                    | none =>
                        rw [hl_b] at h_x1; simp only [EnvVis_aux] at h_x1
                    | some i_b =>
                        rw [hl_b] at h_x1
                        simp only at h_x1
                        rw [hp_a] at h_x1
                        cases hp_b : s_b.heap[i_b]? with
                        | none =>
                            rw [hp_b] at h_x1; simp only at h_x1
                        | some v_b =>
                            refine ⟨v_b, s_b, ?_, ?_, h_ctx,
                                    HeapEvolution.refl _ _, h_env, h_meta,
                                    h_ctx.hv_a i_a v_a hp_a, h_ctx.hv_b i_b v_b hp_b⟩
                            · simp [eval, hl_b, hp_b]
                            · intro depth
                              have h_x_d := h_env depth x
                              rw [hl_a, hl_b] at h_x_d
                              simp only at h_x_d
                              rw [hp_a, hp_b] at h_x_d
                              exact h_x_d
        | lam ps body =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            refine ⟨.closure ps body env_b, s_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, h_meta,
                    h_ctx.ev_a, h_ctx.ev_b⟩
            · simp [eval]
            · intro depth
              cases depth with
              | zero => trivial
              | succ k' =>
                  -- ValVis_aux on closures: requires `cenv_a = cenv_b`
                  -- which here is `env_a = env_b`, given by h_ctx.env_eq.
                  refine ⟨rfl, rfl, h_ctx.env_eq, ?_⟩
                  exact h_env k'
        | installPolicy idx =>
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                refine ⟨.bool false, s_b, ?_, ?_, h_ctx,
                        HeapEvolution.refl _ _, h_env, h_meta, trivial, trivial⟩
                · simp [eval, hp]
                · intro depth
                  cases depth with | zero => trivial | succ _ => rfl
            | some newPolicy =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                -- installPolicy: both states get the same new policy.
                -- Heap unchanged on both sides. StateExt is just policy
                -- equality post-strengthening, which is preserved.
                refine ⟨.bool true, { s_b with policy := newPolicy }, ?_, ?_,
                        ⟨rfl,
                         h_ctx.hv_a, h_ctx.hv_b,
                         h_ctx.ev_a, h_ctx.ev_b,
                         h_ctx.em_a, h_ctx.em_b,
                         hresp_pt idx newPolicy hp,
                         h_ctx.env_eq, h_ctx.heap_len_eq⟩,
                        ⟨Nat.le_refl _, Nat.le_refl _,
                         fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩,
                        h_env, h_meta, trivial, trivial⟩
                · simp [eval, hp]
                · intro depth
                  cases depth with | zero => trivial | succ _ => rfl
        | em body =>
            simp only [eval] at h_eval
            -- IH on body uses metaEnv as env on both sides.
            have h_ctx_meta : WFCtx metaEnv metaEnv metaEnv s_a s_b :=
              ⟨h_ctx.state_ext, h_ctx.hv_a, h_ctx.hv_b,
               h_ctx.em_a, h_ctx.em_b, h_ctx.em_a, h_ctx.em_b,
               h_ctx.policy_resp, rfl, h_ctx.heap_len_eq⟩
            obtain ⟨r_b, s_b', h_eval_b, h_vv, h_ctx', h_he,
                    _h_env_meta, h_meta', hv_ra, hv_rb⟩ :=
              ih_eval ptable body metaEnv metaEnv metaEnv s_a s_b r_a s_a'
                hresp_pt h_ctx_meta h_meta h_meta h_eval
            -- Derive EnvVis env_a env_b s_a'.heap s_b'.heap from h_env via
            -- HeapEvolution's env_preserve property.
            have h_env' : EnvVis env_a env_b s_a'.heap s_b'.heap := by
              intro n
              exact h_he.env_preserve n env_a env_b h_ctx.env_eq
                h_ctx.ev_a h_ctx.ev_b (h_env n)
            -- Lift env validity via length monotonicity.
            have h_ctx_out : WFCtx env_a env_b metaEnv s_a' s_b' :=
              ⟨h_ctx'.state_ext, h_ctx'.hv_a, h_ctx'.hv_b,
               h_ctx.ev_a.length_mono h_he.len_a,
               h_ctx.ev_b.length_mono h_he.len_b,
               h_ctx'.em_a, h_ctx'.em_b,
               h_ctx'.policy_resp, h_ctx.env_eq, h_ctx'.heap_len_eq⟩
            refine ⟨r_b, s_b', ?_, h_vv, h_ctx_out,
                    h_he, h_env', h_meta',
                    hv_ra, hv_rb⟩
            simp [eval, h_eval_b]
        | seq exps =>
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                refine ⟨.nilV, s_b, ?_, ?_, h_ctx,
                        HeapEvolution.refl _ _, h_env, h_meta, trivial, trivial⟩
                · simp [eval]
                · intro depth
                  cases depth with | zero => trivial | succ _ => trivial
            | cons e rest =>
                cases rest with
                | nil =>
                    -- exps = [e]: eval (k+1) (.seq [e]) reduces to eval k e
                    simp only [eval] at h_eval
                    obtain ⟨r_b, s_b', h_eval_b, h_vv, h_ctx', h_he,
                            h_env', h_meta', hv_ra, hv_rb⟩ :=
                      ih_eval ptable e env_a env_b metaEnv s_a s_b r_a s_a'
                        hresp_pt h_ctx h_env h_meta h_eval
                    refine ⟨r_b, s_b', ?_, h_vv, h_ctx', h_he, h_env', h_meta',
                            hv_ra, hv_rb⟩
                    simp [eval, h_eval_b]
                | cons e2 rest2 =>
                    -- exps = e :: e2 :: rest2: eval e then recurse on .seq (e2 :: rest2)
                    simp only [eval] at h_eval
                    cases he : eval k ptable e env_a metaEnv s_a with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨v_e, s_a_inner⟩ := pr
                        rw [he] at h_eval
                        simp only at h_eval
                        obtain ⟨v_e_b, s_b_inner, h_eval_e_b, _h_vv_e, h_ctx_inner,
                                h_he_inner, h_env_inner, h_meta_inner,
                                _hv_ve_a, _hv_ve_b⟩ :=
                          ih_eval ptable e env_a env_b metaEnv s_a s_b v_e s_a_inner
                            hresp_pt h_ctx h_env h_meta he
                        obtain ⟨r_b, s_b', h_eval_seq_b, h_vv, h_ctx', h_he',
                                h_env', h_meta', hv_ra, hv_rb⟩ :=
                          ih_eval ptable (.seq (e2 :: rest2)) env_a env_b metaEnv
                            s_a_inner s_b_inner r_a s_a'
                            hresp_pt h_ctx_inner h_env_inner h_meta_inner h_eval
                        refine ⟨r_b, s_b', ?_, h_vv, h_ctx',
                                HeapEvolution.trans h_he_inner h_he',
                                h_env', h_meta', hv_ra, hv_rb⟩
                        simp [eval, h_eval_e_b, h_eval_seq_b]
        | ifte c t e =>
            simp only [eval] at h_eval
            cases hc : eval k ptable c env_a metaEnv s_a with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv_a, s_c_a⟩ := pr
                rw [hc] at h_eval
                obtain ⟨cv_b, s_c_b, h_eval_c_b, h_vv_c, h_ctx_c, h_he_c,
                        h_env_c, h_meta_c, _hv_cva, _hv_cvb⟩ :=
                  ih_eval ptable c env_a env_b metaEnv s_a s_b cv_a s_c_a
                    hresp_pt h_ctx h_env h_meta hc
                have h_iff : cv_a = .bool false ↔ cv_b = .bool false :=
                  ValVis_bool_false_iff cv_a cv_b s_c_a.heap s_c_b.heap h_vv_c
                by_cases hcv : cv_a = .bool false
                · -- both sides take else-branch
                  have h_cv_b : cv_b = .bool false := h_iff.mp hcv
                  subst hcv
                  simp only at h_eval
                  -- h_eval : eval k ptable e env_a metaEnv s_c_a = some (r_a, s_a')
                  obtain ⟨r_b, s_b', h_eval_e_b, h_vv, h_ctx', h_he',
                          h_env', h_meta', hv_ra, hv_rb⟩ :=
                    ih_eval ptable e env_a env_b metaEnv s_c_a s_c_b r_a s_a'
                      hresp_pt h_ctx_c h_env_c h_meta_c h_eval
                  refine ⟨r_b, s_b', ?_, h_vv, h_ctx',
                          HeapEvolution.trans h_he_c h_he',
                          h_env', h_meta', hv_ra, hv_rb⟩
                  simp [eval, h_eval_c_b, h_cv_b, h_eval_e_b]
                · -- both sides take then-branch
                  have h_cv_b_ne : cv_b ≠ .bool false := fun h => hcv (h_iff.mpr h)
                  -- h_eval reduces via the catchall arm to: eval k ptable t ... = some
                  have h_eval_t : eval k ptable t env_a metaEnv s_c_a = some (r_a, s_a') := by
                    cases cv_a with
                    | bool b =>
                        cases b with
                        | false => exact absurd rfl hcv
                        | true  => exact h_eval
                    | num _            => exact h_eval
                    | nilV             => exact h_eval
                    | cons _ _         => exact h_eval
                    | sym _            => exact h_eval
                    | closure _ _ _    => exact h_eval
                    | prim _           => exact h_eval
                    | builtinBaseApply => exact h_eval
                  obtain ⟨r_b, s_b', h_eval_t_b, h_vv, h_ctx', h_he',
                          h_env', h_meta', hv_ra, hv_rb⟩ :=
                    ih_eval ptable t env_a env_b metaEnv s_c_a s_c_b r_a s_a'
                      hresp_pt h_ctx_c h_env_c h_meta_c h_eval_t
                  refine ⟨r_b, s_b', ?_, h_vv, h_ctx',
                          HeapEvolution.trans h_he_c h_he',
                          h_env', h_meta', hv_ra, hv_rb⟩
                  -- Goal: eval (k+1) (.ifte c t e) env_b metaEnv s_b = some (r_b, s_b')
                  -- Reduces to match eval k c env_b metaEnv s_b with ...
                  -- = match (some (cv_b, s_c_b)) with ... → t branch (since cv_b ≠ .bool false)
                  simp only [eval, h_eval_c_b]
                  cases cv_b with
                  | bool b =>
                      cases b with
                      | false => exact absurd rfl h_cv_b_ne
                      | true  => exact h_eval_t_b
                  | num _            => exact h_eval_t_b
                  | nilV             => exact h_eval_t_b
                  | cons _ _         => exact h_eval_t_b
                  | sym _            => exact h_eval_t_b
                  | closure _ _ _    => exact h_eval_t_b
                  | prim _           => exact h_eval_t_b
                  | builtinBaseApply => exact h_eval_t_b
        | app exps =>
            cases exps with
            | nil =>
                simp only [eval] at h_eval
                exact absurd h_eval (by simp)
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable f env_a metaEnv s_a with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv_a, s_a_inner⟩ := pr
                    rw [hf] at h_eval
                    simp only at h_eval
                    -- IH on f
                    obtain ⟨fv_b, s_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1,
                            h_env1, h_meta1, hv_fva, hv_fvb⟩ :=
                      ih_eval ptable f env_a env_b metaEnv s_a s_b fv_a s_a_inner
                        hresp_pt h_ctx h_env h_meta hf
                    cases ha : evalList k ptable args env_a metaEnv s_a_inner with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs_a, s_a_inner2⟩ := pr2
                        rw [ha] at h_eval
                        simp only at h_eval
                        -- IH on args
                        obtain ⟨avs_b, s_b_inner2, h_eval_args_b, h_lvv, h_ctx2, h_he2,
                                h_env2, h_meta2, hv_avsa, hv_avsb⟩ :=
                          ih_evalList ptable args env_a env_b metaEnv s_a_inner s_b_inner
                            avs_a s_a_inner2 hresp_pt h_ctx1 h_env1 h_meta1 ha
                        -- WFCtx metaEnv metaEnv metaEnv at s_a_inner2 s_b_inner2
                        have h_ctx_meta2 : WFCtx metaEnv metaEnv metaEnv s_a_inner2 s_b_inner2 :=
                          ⟨h_ctx2.state_ext, h_ctx2.hv_a, h_ctx2.hv_b,
                           h_ctx2.em_a, h_ctx2.em_b, h_ctx2.em_a, h_ctx2.em_b,
                           h_ctx2.policy_resp, rfl, h_ctx2.heap_len_eq⟩
                        -- Lift ValVis fv_a fv_b across the inner→inner2 evolution.
                        have h_vv_f' : ValVis fv_a fv_b s_a_inner2.heap s_b_inner2.heap :=
                          h_he2.valVis_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
                        have hv_fva2 : ValValid fv_a s_a_inner2.heap :=
                          ValValid.length_mono fv_a hv_fva h_he2.len_a
                        have hv_fvb2 : ValValid fv_b s_b_inner2.heap :=
                          ValValid.length_mono fv_b hv_fvb h_he2.len_b
                        obtain ⟨r_b, s_b', h_eval_av_b, h_vv, h_ctx3, h_he3,
                                h_meta3, hv_ra, hv_rb⟩ :=
                          ih_applyVia ptable fv_a fv_b avs_a avs_b metaEnv
                            s_a_inner2 s_b_inner2 r_a s_a'
                            hresp_pt h_ctx_meta2 h_vv_f' h_lvv h_meta2
                            hv_fva2 hv_fvb2 hv_avsa hv_avsb h_eval
                        have h_he_chain : HeapEvolution s_a s_b s_a' s_b' :=
                          HeapEvolution.trans h_he1 (HeapEvolution.trans h_he2 h_he3)
                        have h_ctx_out : WFCtx env_a env_b metaEnv s_a' s_b' :=
                          ⟨h_ctx3.state_ext, h_ctx3.hv_a, h_ctx3.hv_b,
                           h_ctx.ev_a.length_mono h_he_chain.len_a,
                           h_ctx.ev_b.length_mono h_he_chain.len_b,
                           h_ctx3.em_a, h_ctx3.em_b,
                           h_ctx3.policy_resp, h_ctx.env_eq, h_ctx3.heap_len_eq⟩
                        have h_env_out : EnvVis env_a env_b s_a'.heap s_b'.heap :=
                          h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                            h_ctx.ev_a h_ctx.ev_b h_env
                        refine ⟨r_b, s_b', ?_, h_vv, h_ctx_out,
                                h_he_chain, h_env_out, h_meta3,
                                hv_ra, hv_rb⟩
                        simp [eval, h_eval_f_b, h_eval_args_b, h_eval_av_b]
        | primApp f args =>
            simp only [eval] at h_eval
            cases hf : eval k ptable f env_a metaEnv s_a with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv_a, s_a_inner⟩ := pr
                rw [hf] at h_eval
                simp only at h_eval
                -- IH on f
                obtain ⟨fv_b, s_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1,
                        h_env1, h_meta1, hv_fva, hv_fvb⟩ :=
                  ih_eval ptable f env_a env_b metaEnv s_a s_b fv_a s_a_inner
                    hresp_pt h_ctx h_env h_meta hf
                cases ha : evalList k ptable args env_a metaEnv s_a_inner with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs_a, s_a_inner2⟩ := pr2
                    rw [ha] at h_eval
                    simp only at h_eval
                    obtain ⟨avs_b, s_b_inner2, h_eval_args_b, h_lvv, h_ctx2, h_he2,
                            h_env2, h_meta2, hv_avsa, hv_avsb⟩ :=
                      ih_evalList ptable args env_a env_b metaEnv s_a_inner s_b_inner
                        avs_a s_a_inner2 hresp_pt h_ctx1 h_env1 h_meta1 ha
                    have h_ctx_meta2 : WFCtx metaEnv metaEnv metaEnv s_a_inner2 s_b_inner2 :=
                      ⟨h_ctx2.state_ext, h_ctx2.hv_a, h_ctx2.hv_b,
                       h_ctx2.em_a, h_ctx2.em_b, h_ctx2.em_a, h_ctx2.em_b,
                       h_ctx2.policy_resp, rfl, h_ctx2.heap_len_eq⟩
                    have h_vv_f' : ValVis fv_a fv_b s_a_inner2.heap s_b_inner2.heap :=
                      h_he2.valVis_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
                    have hv_fva2 : ValValid fv_a s_a_inner2.heap :=
                      ValValid.length_mono fv_a hv_fva h_he2.len_a
                    have hv_fvb2 : ValValid fv_b s_b_inner2.heap :=
                      ValValid.length_mono fv_b hv_fvb h_he2.len_b
                    obtain ⟨r_b, s_b', h_eval_av_b, h_vv, h_ctx3, h_he3,
                            h_meta3, hv_ra, hv_rb⟩ :=
                      ih_applyDirect ptable fv_a fv_b avs_a avs_b metaEnv
                        s_a_inner2 s_b_inner2 r_a s_a'
                        hresp_pt h_ctx_meta2 h_vv_f' h_lvv h_meta2
                        hv_fva2 hv_fvb2 hv_avsa hv_avsb h_eval
                    have h_he_chain : HeapEvolution s_a s_b s_a' s_b' :=
                      HeapEvolution.trans h_he1 (HeapEvolution.trans h_he2 h_he3)
                    have h_ctx_out : WFCtx env_a env_b metaEnv s_a' s_b' :=
                      ⟨h_ctx3.state_ext, h_ctx3.hv_a, h_ctx3.hv_b,
                       h_ctx.ev_a.length_mono h_he_chain.len_a,
                       h_ctx.ev_b.length_mono h_he_chain.len_b,
                       h_ctx3.em_a, h_ctx3.em_b,
                       h_ctx3.policy_resp, h_ctx.env_eq, h_ctx3.heap_len_eq⟩
                    have h_env_out : EnvVis env_a env_b s_a'.heap s_b'.heap :=
                      h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                        h_ctx.ev_a h_ctx.ev_b h_env
                    refine ⟨r_b, s_b', ?_, h_vv, h_ctx_out,
                            h_he_chain, h_env_out, h_meta3,
                            hv_ra, hv_rb⟩
                    simp [eval, h_eval_f_b, h_eval_args_b, h_eval_av_b]
        | set x e =>
            -- The `.set x e` case. With `env_eq` (env_a = env_b) and
            -- `heap_len_eq` (s_a.heap.length = s_b.heap.length) from
            -- `WFCtx`, `env.lookup x` produces the same `idx` on both
            -- sides, `isMetaMutation` agrees cross-side, and the
            -- gate's admit decision agrees by `policy_resp`. The
            -- `HeapEvolution` post-condition follows from a
            -- depth-induction `ValVis_aux_update` / `EnvVis_aux_update`
            -- (with the "mixed-index" cases vacuously unreachable
            -- under the `env_eq` invariant).
            simp only [eval] at h_eval
            cases he : eval k ptable e env_a metaEnv s_a with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_a, s_a_inner⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                -- IH on e gives the inner-state framing for `e`.
                obtain ⟨v_b, s_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner,
                        h_env_inner, h_meta_inner, hv_va, hv_vb⟩ :=
                  ih_eval ptable e env_a env_b metaEnv s_a s_b v_a s_a_inner
                    hresp_pt h_ctx h_env h_meta he
                -- env.lookup x: same on both sides via env_eq.
                cases hl : env_a.lookup x with
                | none =>
                    -- env.lookup x = none contradicts h_eval (which is
                    -- some). The `.set` body doesn't progress past the
                    -- env-lookup step.
                    rw [hl] at h_eval; simp at h_eval
                | some idx =>
                    rw [hl] at h_eval
                    simp only at h_eval
                    have hl_b : env_b.lookup x = some idx := by
                      rw [← h_ctx.env_eq]; exact hl
                    -- The "self-update preserves universal-depth bisim"
                    -- precondition for `ValVis_aux_update` /
                    -- `EnvVis_aux_update`. This is a separate small
                    -- depth-induction lemma (not yet proved): given
                    -- `ValVis v_a v_b at OLD heaps`, conclude
                    -- `ValVis v_a v_b at NEW heaps` (where NEW is OLD
                    -- with idx updated to v_a / v_b respectively). The
                    -- four sub-cases below all rely on this. Punted as
                    -- a single small lemma to be filled in.
                    have h_vis_v_at_new :
                        ∀ k, ValVis_aux k v_a v_b
                              (s_a_inner.heap.update idx v_a)
                              (s_b_inner.heap.update idx v_b) := by
                      sorry  -- self-update preserves bisim (provable by
                             -- depth induction on k using the existing
                             -- `ValVis_aux_update` infrastructure).
                    have hv_va_new :
                        ValValid v_a (s_a_inner.heap.update idx v_a) :=
                      ValValid.length_mono v_a hv_va
                        (Heap.update_length s_a_inner.heap idx v_a ▸ Nat.le_refl _)
                    have hv_vb_new :
                        ValValid v_b (s_b_inner.heap.update idx v_b) :=
                      ValValid.length_mono v_b hv_vb
                        (Heap.update_length s_b_inner.heap idx v_b ▸ Nat.le_refl _)
                    -- A small helper: HeapEvolution from a self-update at
                    -- `idx` (used in plain mutation and in the meta-accept
                    -- case). The two sides update at the *same* idx (by
                    -- env_eq → env_a.lookup x = env_b.lookup x = some idx)
                    -- to bisim-related new values v_a, v_b.
                    have h_he_update :
                        HeapEvolution s_a_inner s_b_inner
                          { s_a_inner with heap := s_a_inner.heap.update idx v_a }
                          { s_b_inner with heap := s_b_inner.heap.update idx v_b } := by
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · show s_a_inner.heap.length ≤
                            (s_a_inner.heap.update idx v_a).length
                        rw [Heap.update_length]; exact Nat.le_refl _
                      · show s_b_inner.heap.length ≤
                            (s_b_inner.heap.update idx v_b).length
                        rw [Heap.update_length]; exact Nat.le_refl _
                      · intro nE env_a' env_b' h_env_eq' hev_a' hev_b' h_env_vis
                        -- Apply EnvVis_aux_update at depth nE. The
                        -- env_eq precondition (h_env_eq') is exactly
                        -- the new structural constraint we added.
                        exact EnvVis_aux_update nE env_a' env_b'
                          s_a_inner.heap s_b_inner.heap idx v_a v_b
                          h_ctx_inner.hv_a h_ctx_inner.hv_b
                          h_ctx_inner.heap_len_eq hev_a' hev_b'
                          h_env_eq' h_vis_v_at_new
                          hv_va_new hv_vb_new h_env_vis
                      · intro nV v_x v_y hv_x hv_y h_v_vis
                        -- Apply ValVis_aux_update at depth nV on (v_x, v_y).
                        exact ValVis_aux_update nV v_x v_y
                          s_a_inner.heap s_b_inner.heap idx v_a v_b
                          h_ctx_inner.hv_a h_ctx_inner.hv_b
                          h_ctx_inner.heap_len_eq hv_x hv_y
                          h_vis_v_at_new hv_va_new hv_vb_new h_v_vis
                    -- Now case-analyze on isMetaMutation x env_a metaEnv.
                    by_cases h_meta_mut : isMetaMutation x env_a metaEnv = true
                    · -- META MUTATION CASE.
                      have h_meta_mut_b : isMetaMutation x env_b metaEnv = true := by
                        unfold isMetaMutation at h_meta_mut ⊢
                        rw [hl] at h_meta_mut; rw [hl_b]
                        exact h_meta_mut
                      -- The meta-mutation case needs:
                      --   1. Derive `metaEnv.lookup x = some idx` from
                      --      `isMetaMutation = true`.
                      --   2. From `EnvVis metaEnv metaEnv` at the inner
                      --      state pair, get `oldVal_a, oldVal_b` bisim
                      --      at idx on each side.
                      --   3. Apply `policy_resp` to conclude same gate
                      --      decision (after relating `s_a.policy` =
                      --      `s_a_inner.policy` via the eval-doesn't-
                      --      change-policy lemma — easy except for
                      --      nested .installPolicy in the RHS, which is
                      --      a separate observation).
                      --   4. Branch on accept/reject; admit uses
                      --      `h_he_update`, reject uses `h_he_inner`.
                      -- Punted as a localized sorry while we lock in
                      -- the plain mutation case.
                      sorry
                    · -- PLAIN MUTATION CASE: not gated, both sides return
                      -- (.bool true, heap.update idx v).
                      have h_meta_mut_b_eq : isMetaMutation x env_b metaEnv =
                          isMetaMutation x env_a metaEnv := by
                        rw [h_ctx.env_eq]
                      have h_meta_mut_b_false :
                          isMetaMutation x env_b metaEnv = false := by
                        rw [h_meta_mut_b_eq]; cases h_dec : isMetaMutation x env_a metaEnv
                        · rfl
                        · exact absurd h_dec h_meta_mut
                      have h_meta_mut_a_false :
                          isMetaMutation x env_a metaEnv = false := by
                        cases h_dec : isMetaMutation x env_a metaEnv
                        · rfl
                        · exact absurd h_dec h_meta_mut
                      rw [h_meta_mut_a_false] at h_eval
                      simp only [Bool.false_eq_true, ↓reduceIte,
                                 Option.some.injEq, Prod.mk.injEq] at h_eval
                      obtain ⟨h_r, h_s⟩ := h_eval
                      subst h_r; subst h_s
                      -- Compose HeapEvolution: inner step + update step.
                      have h_he_chain : HeapEvolution s_a s_b
                          { s_a_inner with heap := s_a_inner.heap.update idx v_a }
                          { s_b_inner with heap := s_b_inner.heap.update idx v_b } :=
                        HeapEvolution.trans h_he_inner h_he_update
                      -- Output WFCtx. The HeapValid claims for the
                      -- updated heaps follow from validity of v_a, v_b
                      -- (which are validly placed at idx) and validity
                      -- of unchanged cells (carried from h_ctx_inner).
                      have h_len_a : s_a_inner.heap.length =
                          (s_a_inner.heap.update idx v_a).length :=
                        (Heap.update_length _ _ _).symm
                      have h_len_b : s_b_inner.heap.length =
                          (s_b_inner.heap.update idx v_b).length :=
                        (Heap.update_length _ _ _).symm
                      have h_le_a : s_a_inner.heap.length ≤
                          (s_a_inner.heap.update idx v_a).length :=
                        Nat.le_of_eq h_len_a
                      have h_le_b : s_b_inner.heap.length ≤
                          (s_b_inner.heap.update idx v_b).length :=
                        Nat.le_of_eq h_len_b
                      have hh_a_new : HeapValid (s_a_inner.heap.update idx v_a) := by
                        intro i v hp
                        by_cases h_ieq : i = idx
                        · subst h_ieq
                          rw [Heap.update_get_eq _ _ _
                              (h_ctx_inner.ev_a x i hl)] at hp
                          simp only [Option.some.injEq] at hp
                          subst hp
                          exact ValValid.length_mono v_a hv_va h_le_a
                        · rw [Heap.update_get_neq _ _ _ _ h_ieq] at hp
                          have hv_old := h_ctx_inner.hv_a i v hp
                          exact ValValid.length_mono v hv_old h_le_a
                      have hh_b_new : HeapValid (s_b_inner.heap.update idx v_b) := by
                        intro i v hp
                        by_cases h_ieq : i = idx
                        · subst h_ieq
                          rw [Heap.update_get_eq _ _ _
                              (h_ctx_inner.ev_b x i hl_b)] at hp
                          simp only [Option.some.injEq] at hp
                          subst hp
                          exact ValValid.length_mono v_b hv_vb h_le_b
                        · rw [Heap.update_get_neq _ _ _ _ h_ieq] at hp
                          have hv_old := h_ctx_inner.hv_b i v hp
                          exact ValValid.length_mono v hv_old h_le_b
                      have h_ctx_out :
                          WFCtx env_a env_b metaEnv
                            { s_a_inner with heap := s_a_inner.heap.update idx v_a }
                            { s_b_inner with heap := s_b_inner.heap.update idx v_b } := by
                        refine ⟨h_ctx_inner.state_ext, hh_a_new, hh_b_new,
                                ?_, ?_, ?_, ?_, h_ctx_inner.policy_resp,
                                h_ctx_inner.env_eq, ?_⟩
                        · exact EnvValid.length_mono h_ctx_inner.ev_a h_le_a
                        · exact EnvValid.length_mono h_ctx_inner.ev_b h_le_b
                        · exact EnvValid.length_mono h_ctx_inner.em_a h_le_a
                        · exact EnvValid.length_mono h_ctx_inner.em_b h_le_b
                        · simp [Heap.update_length, h_ctx_inner.heap_len_eq]
                      have h_env_out : EnvVis env_a env_b
                          (s_a_inner.heap.update idx v_a)
                          (s_b_inner.heap.update idx v_b) :=
                        h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                          h_ctx.ev_a h_ctx.ev_b h_env
                      have h_meta_out : EnvVis metaEnv metaEnv
                          (s_a_inner.heap.update idx v_a)
                          (s_b_inner.heap.update idx v_b) :=
                        h_he_chain.envVis_preserve metaEnv metaEnv rfl
                          h_ctx.em_a h_ctx.em_b h_meta
                      refine ⟨.bool true,
                              { s_b_inner with heap := s_b_inner.heap.update idx v_b },
                              ?_,
                              -- ValVis on (.bool true, .bool true): trivial.
                              (fun d => by cases d with
                                | zero => trivial
                                | succ _ => rfl),
                              h_ctx_out, h_he_chain, h_env_out, h_meta_out,
                              trivial, trivial⟩
                      simp [eval, h_eval_e_b, hl_b, h_meta_mut_b_false]
        | letE x e body =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env_a metaEnv s_a with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_a, s_a_inner⟩ := pr
                rw [he] at h_eval
                -- IH on e
                obtain ⟨v_b, s_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner,
                        h_env_inner, h_meta_inner, hv_va, hv_vb⟩ :=
                  ih_eval ptable e env_a env_b metaEnv s_a s_b v_a s_a_inner
                    hresp_pt h_ctx h_env h_meta he
                -- After eval e, we alloc v on each side. The let-destructured
                -- alloc reduces by Heap.alloc def: (h ++ [v], h.length).
                simp only [Heap.alloc] at h_eval
                -- Heap lookups at the fresh indices.
                have h_lookup_a :
                    (s_a_inner.heap ++ [v_a])[s_a_inner.heap.length]? = some v_a := by
                  rw [List.getElem?_append_right (Nat.le_refl _)]; simp
                have h_lookup_b :
                    (s_b_inner.heap ++ [v_b])[s_b_inner.heap.length]? = some v_b := by
                  rw [List.getElem?_append_right (Nat.le_refl _)]; simp
                -- HeapValid on the alloc heaps.
                have hh_a_alloc : HeapValid (s_a_inner.heap ++ [v_a]) := by
                  intro i v hp
                  by_cases h_lt : i < s_a_inner.heap.length
                  · have hp_old : s_a_inner.heap[i]? = some v := by
                      have heq := getElem?_prefix s_a_inner.heap [v_a] i h_lt
                      rw [← heq]; exact hp
                    exact ValValid.heap_extends v (h_ctx_inner.hv_a i v hp_old)
                      ⟨[v_a], rfl⟩
                  · have h_eq : i = s_a_inner.heap.length := by
                      have h_le : i < (s_a_inner.heap ++ [v_a]).length := by
                        rw [List.getElem?_eq_some_iff] at hp
                        obtain ⟨h, _⟩ := hp; exact h
                      simp [List.length_append] at h_le; omega
                    subst h_eq
                    rw [h_lookup_a] at hp
                    simp only [Option.some.injEq] at hp
                    subst hp
                    exact ValValid.heap_extends v_a hv_va ⟨[v_a], rfl⟩
                have hh_b_alloc : HeapValid (s_b_inner.heap ++ [v_b]) := by
                  intro i v hp
                  by_cases h_lt : i < s_b_inner.heap.length
                  · have hp_old : s_b_inner.heap[i]? = some v := by
                      have heq := getElem?_prefix s_b_inner.heap [v_b] i h_lt
                      rw [← heq]; exact hp
                    exact ValValid.heap_extends v (h_ctx_inner.hv_b i v hp_old)
                      ⟨[v_b], rfl⟩
                  · have h_eq : i = s_b_inner.heap.length := by
                      have h_le : i < (s_b_inner.heap ++ [v_b]).length := by
                        rw [List.getElem?_eq_some_iff] at hp
                        obtain ⟨h, _⟩ := hp; exact h
                      simp [List.length_append] at h_le; omega
                    subst h_eq
                    rw [h_lookup_b] at hp
                    simp only [Option.some.injEq] at hp
                    subst hp
                    exact ValValid.heap_extends v_b hv_vb ⟨[v_b], rfl⟩
                -- EnvValid the cons-extended envs in the alloc heaps.
                have hev_a' : EnvValid (.cons x s_a_inner.heap.length env_a)
                    (s_a_inner.heap ++ [v_a]) := by
                  intro name i hl
                  simp only [List.length_append, List.length_singleton]
                  simp only [Env.lookup] at hl
                  by_cases h_eq : x = name
                  · subst h_eq
                    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                    omega
                  · have h_neq : (x == name) = false := by
                      rw [beq_eq_false_iff_ne]; exact h_eq
                    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                    have := h_ctx_inner.ev_a name i hl
                    omega
                have hev_b' : EnvValid (.cons x s_b_inner.heap.length env_b)
                    (s_b_inner.heap ++ [v_b]) := by
                  intro name i hl
                  simp only [List.length_append, List.length_singleton]
                  simp only [Env.lookup] at hl
                  by_cases h_eq : x = name
                  · subst h_eq
                    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                    omega
                  · have h_neq : (x == name) = false := by
                      rw [beq_eq_false_iff_ne]; exact h_eq
                    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                    have := h_ctx_inner.ev_b name i hl
                    omega
                have hem_a' : EnvValid metaEnv (s_a_inner.heap ++ [v_a]) :=
                  EnvValid.heap_extends h_ctx_inner.em_a ⟨[v_a], rfl⟩
                have hem_b' : EnvValid metaEnv (s_b_inner.heap ++ [v_b]) :=
                  EnvValid.heap_extends h_ctx_inner.em_b ⟨[v_b], rfl⟩
                -- WFCtx for the body call (with the cons-extended envs and alloc states).
                -- Cons-extended envs match cross-side: same name `x`,
                -- same alloc index (heap_len_eq), same outer env (env_eq).
                have h_cons_eq :
                    (.cons x s_a_inner.heap.length env_a : Env)
                      = (.cons x s_b_inner.heap.length env_b) := by
                  rw [h_ctx_inner.env_eq, h_ctx_inner.heap_len_eq]
                have h_alloc_len_eq :
                    (s_a_inner.heap ++ [v_a]).length =
                      (s_b_inner.heap ++ [v_b]).length := by
                  simp [List.length_append, h_ctx_inner.heap_len_eq]
                have h_ctx_alloc :
                    WFCtx (.cons x s_a_inner.heap.length env_a)
                      (.cons x s_b_inner.heap.length env_b) metaEnv
                      { s_a_inner with heap := s_a_inner.heap ++ [v_a] }
                      { s_b_inner with heap := s_b_inner.heap ++ [v_b] } :=
                  ⟨h_ctx_inner.state_ext, hh_a_alloc, hh_b_alloc,
                   hev_a', hev_b', hem_a', hem_b',
                   h_ctx_inner.policy_resp, h_cons_eq, h_alloc_len_eq⟩
                -- ValVis v_a v_b lifted to alloc heaps.
                have h_vv_v_alloc :
                    ValVis v_a v_b (s_a_inner.heap ++ [v_a]) (s_b_inner.heap ++ [v_b]) :=
                  ValVis_extends v_a v_b s_a_inner.heap s_b_inner.heap [v_a] [v_b]
                    h_ctx_inner.hv_a h_ctx_inner.hv_b hv_va hv_vb h_vv_v
                -- EnvVis env_a env_b at alloc heaps.
                have h_env_alloc :
                    EnvVis env_a env_b (s_a_inner.heap ++ [v_a]) (s_b_inner.heap ++ [v_b]) :=
                  EnvVis_extends env_a env_b s_a_inner.heap s_b_inner.heap [v_a] [v_b]
                    h_ctx_inner.hv_a h_ctx_inner.hv_b h_ctx_inner.ev_a h_ctx_inner.ev_b
                    h_env_inner
                -- EnvVis on cons-extended envs at alloc heaps.
                have h_env' :
                    EnvVis (.cons x s_a_inner.heap.length env_a)
                      (.cons x s_b_inner.heap.length env_b)
                      (s_a_inner.heap ++ [v_a]) (s_b_inner.heap ++ [v_b]) :=
                  EnvVis_cons x s_a_inner.heap.length s_b_inner.heap.length env_a env_b
                    (s_a_inner.heap ++ [v_a]) (s_b_inner.heap ++ [v_b]) v_a v_b
                    h_lookup_a h_lookup_b h_vv_v_alloc h_env_alloc
                -- EnvVis metaEnv metaEnv at alloc heaps.
                have h_meta_alloc :
                    EnvVis metaEnv metaEnv
                      (s_a_inner.heap ++ [v_a]) (s_b_inner.heap ++ [v_b]) :=
                  EnvVis_extends metaEnv metaEnv s_a_inner.heap s_b_inner.heap [v_a] [v_b]
                    h_ctx_inner.hv_a h_ctx_inner.hv_b h_ctx_inner.em_a h_ctx_inner.em_b
                    h_meta_inner
                -- Now apply IH on body.
                obtain ⟨r_b, s_b', h_eval_b_b, h_vv_r, h_ctx_body, h_he_body,
                        _h_env_body, h_meta_body, hv_ra, hv_rb⟩ :=
                  ih_eval ptable body
                    (.cons x s_a_inner.heap.length env_a)
                    (.cons x s_b_inner.heap.length env_b) metaEnv
                    { s_a_inner with heap := s_a_inner.heap ++ [v_a] }
                    { s_b_inner with heap := s_b_inner.heap ++ [v_b] } r_a s_a'
                    hresp_pt h_ctx_alloc h_env' h_meta_alloc h_eval
                -- Build the alloc step's HeapEvolution and compose the chain.
                have h_he_alloc :
                    HeapEvolution s_a_inner s_b_inner
                      { s_a_inner with heap := s_a_inner.heap ++ [v_a] }
                      { s_b_inner with heap := s_b_inner.heap ++ [v_b] } :=
                  HeapEvolution.from_heapExt h_ctx_inner.hv_a h_ctx_inner.hv_b
                    ⟨[v_a], rfl⟩ ⟨[v_b], rfl⟩
                have h_he_chain : HeapEvolution s_a s_b s_a' s_b' :=
                  HeapEvolution.trans h_he_inner
                    (HeapEvolution.trans h_he_alloc h_he_body)
                have h_ctx_out : WFCtx env_a env_b metaEnv s_a' s_b' :=
                  ⟨h_ctx_body.state_ext, h_ctx_body.hv_a, h_ctx_body.hv_b,
                   h_ctx.ev_a.length_mono h_he_chain.len_a,
                   h_ctx.ev_b.length_mono h_he_chain.len_b,
                   h_ctx_body.em_a, h_ctx_body.em_b,
                   h_ctx_body.policy_resp, h_ctx.env_eq, h_ctx_body.heap_len_eq⟩
                have h_env_out : EnvVis env_a env_b s_a'.heap s_b'.heap :=
                  h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                    h_ctx.ev_a h_ctx.ev_b h_env
                refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx_out,
                        h_he_chain, h_env_out, h_meta_body,
                        hv_ra, hv_rb⟩
                -- Goal: eval (k+1) (.letE x e body) env_b metaEnv s_b = some (r_b, s_b')
                simp only [eval, h_eval_e_b, Heap.alloc]
                exact h_eval_b_b
      · -- evalList (k+1)
        intro ptable exps env_a env_b metaEnv s_a s_b rs_a s_a' hresp_pt h_ctx h_env h_meta h_eval
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            refine ⟨[], s_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, h_meta, trivial, trivial⟩
            · simp [evalList]
            · trivial
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable e env_a metaEnv s_a with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_a, s_a_inner⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                cases hrest : evalList k ptable rest env_a metaEnv s_a_inner with
                | none => rw [hrest] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨vs_a, s_a_inner2⟩ := pr2
                    rw [hrest] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_r, h_s⟩ := h_eval
                    subst h_r; subst h_s
                    -- IH on e
                    obtain ⟨v_b, s_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner,
                            h_env_inner, h_meta_inner, hv_va, hv_vb⟩ :=
                      ih_eval ptable e env_a env_b metaEnv s_a s_b v_a s_a_inner
                        hresp_pt h_ctx h_env h_meta he
                    -- IH on rest
                    obtain ⟨vs_b, s_b_inner2, h_eval_rest_b, h_lvv, h_ctx_inner2,
                            h_he_inner2, h_env_inner2, h_meta_inner2,
                            hv_vsa, hv_vsb⟩ :=
                      ih_evalList ptable rest env_a env_b metaEnv s_a_inner s_b_inner
                        vs_a s_a_inner2 hresp_pt h_ctx_inner h_env_inner h_meta_inner hrest
                    -- Lift ValVis v_a v_b and ValValid via HeapEvolution preservation.
                    have h_vv_v' : ValVis v_a v_b s_a_inner2.heap s_b_inner2.heap :=
                      h_he_inner2.valVis_preserve v_a v_b hv_va hv_vb h_vv_v
                    have hv_va' : ValValid v_a s_a_inner2.heap :=
                      ValValid.length_mono v_a hv_va h_he_inner2.len_a
                    have hv_vb' : ValValid v_b s_b_inner2.heap :=
                      ValValid.length_mono v_b hv_vb h_he_inner2.len_b
                    have h_he_chain : HeapEvolution s_a s_b s_a_inner2 s_b_inner2 :=
                      HeapEvolution.trans h_he_inner h_he_inner2
                    refine ⟨v_b :: vs_b, s_b_inner2, ?_,
                            ⟨h_vv_v', h_lvv⟩, h_ctx_inner2,
                            h_he_chain,
                            h_env_inner2, h_meta_inner2,
                            ⟨hv_va', hv_vsa⟩, ⟨hv_vb', hv_vsb⟩⟩
                    simp [evalList, h_eval_e_b, h_eval_rest_b]
      · -- applyVia (k+1)
        intro ptable op_a op_b args_a args_b metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_op
              h_lvv h_meta hv_opa hv_opb hv_argsa hv_argsb h_eval
        simp only [applyVia] at h_eval
        cases hl : metaEnv.lookup "base-apply" with
        | none =>
            rw [hl] at h_eval
            -- both sides go through applyDirect on (op, args) directly
            obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he', h_meta',
                    hv_ra, hv_rb⟩ :=
              ih_applyDirect ptable op_a op_b args_a args_b metaEnv s_a s_b r_a s_a'
                hresp_pt h_ctx h_vv_op h_lvv h_meta hv_opa hv_opb hv_argsa hv_argsb h_eval
            refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he', h_meta', hv_ra, hv_rb⟩
            simp [applyVia, hl, h_eval_b]
        | some idx =>
            rw [hl] at h_eval
            simp only at h_eval
            cases hp_a : s_a.heap[idx]? with
            | none =>
                -- a-side returns none → contradicts h_eval
                rw [hp_a] at h_eval; simp at h_eval
            | some v_a =>
                cases hp_b : s_b.heap[idx]? with
                | none =>
                    -- b-side has none; EnvVis-via-metaEnv forces a-side none too,
                    -- contradiction since a-side is some.
                    have h_meta_d1 := h_meta 1 "base-apply"
                    simp only [EnvVis_aux, hl, hp_a, hp_b] at h_meta_d1
                | some v_b =>
                    rw [hp_a] at h_eval
                    -- Universal-depth ValVis from EnvVis on metaEnv at "base-apply".
                    have h_vv_v : ValVis v_a v_b s_a.heap s_b.heap := by
                      intro d
                      have := h_meta d "base-apply"
                      simp only [EnvVis_aux, hl, hp_a, hp_b] at this
                      exact this
                    -- ValVis_aux 1 to determine v_b's constructor.
                    have h_meta_d1 : ValVis_aux 1 v_a v_b s_a.heap s_b.heap := h_vv_v 1
                    -- ValValid v_a / v_b from heap validity.
                    have hv_va : ValValid v_a s_a.heap := h_ctx.hv_a idx v_a hp_a
                    have hv_vb : ValValid v_b s_b.heap := h_ctx.hv_b idx v_b hp_b
                    -- Case-analyze on v_a's constructor (matches the pattern in applyVia).
                    -- v_b's constructor is forced to match by ValVis_aux 1.
                    cases v_a with
                    | builtinBaseApply =>
                        -- a-side: applyDirect k ptable op_a args_a metaEnv s_a
                        -- v_b must also be .builtinBaseApply (by h_meta_d1 at depth 1).
                        have h_vb : v_b = .builtinBaseApply := by
                          cases v_b with
                          | builtinBaseApply => rfl
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        simp only at h_eval
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable op_a op_b args_a args_b metaEnv
                            s_a s_b r_a s_a' hresp_pt h_ctx h_vv_op h_lvv h_meta
                            hv_opa hv_opb hv_argsa hv_argsb h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | num n =>
                        -- v_a is .num — but the pattern match in applyVia takes the
                        -- catchall: applyDirect on .num n with [op, listToVal args].
                        -- v_b must also be .num n by ValVis_aux 1.
                        have h_vb : v_b = .num n := by
                          cases v_b with
                          | num n' =>
                              have : n = n' := by simp [ValVis_aux] at h_meta_d1; exact h_meta_d1
                              subst this; rfl
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        -- Build the inner ListValVis and ValValid for [op, listToVal args].
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a :
                            ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b :
                            ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.num n) (.num n)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | bool b =>
                        have h_vb : v_b = .bool b := by
                          cases v_b with
                          | bool b' =>
                              have : b = b' := by simp [ValVis_aux] at h_meta_d1; exact h_meta_d1
                              subst this; rfl
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a :
                            ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b :
                            ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.bool b) (.bool b)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | nilV =>
                        have h_vb : v_b = .nilV := by
                          cases v_b with
                          | nilV => rfl
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a : ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b : ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable .nilV .nilV
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | sym str =>
                        have h_vb : v_b = .sym str := by
                          cases v_b with
                          | sym s' =>
                              have : str = s' := by simp [ValVis_aux] at h_meta_d1; exact h_meta_d1
                              subst this; rfl
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a : ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b : ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.sym str) (.sym str)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | prim str =>
                        have h_vb : v_b = .prim str := by
                          cases v_b with
                          | prim s' =>
                              have : str = s' := by simp [ValVis_aux] at h_meta_d1; exact h_meta_d1
                              subst this; rfl
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        subst h_vb
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a : ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b : ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.prim str) (.prim str)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | cons xa ya =>
                        -- v_b is also a cons by ValVis_aux 1.
                        have h_vb : ∃ xb yb, v_b = .cons xb yb := by
                          cases v_b with
                          | cons xb yb => exact ⟨xb, yb, rfl⟩
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | closure _ _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        obtain ⟨xb, yb, h_eq⟩ := h_vb
                        subst h_eq
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a : ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b : ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.cons xa ya) (.cons xb yb)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
                    | closure psa bdya cenva =>
                        have h_vb : ∃ psb bdyb cenvb, v_b = .closure psb bdyb cenvb := by
                          cases v_b with
                          | closure psb bdyb cenvb => exact ⟨psb, bdyb, cenvb, rfl⟩
                          | num _ => simp [ValVis_aux] at h_meta_d1
                          | bool _ => simp [ValVis_aux] at h_meta_d1
                          | nilV => simp [ValVis_aux] at h_meta_d1
                          | sym _ => simp [ValVis_aux] at h_meta_d1
                          | cons _ _ => simp [ValVis_aux] at h_meta_d1
                          | prim _ => simp [ValVis_aux] at h_meta_d1
                          | builtinBaseApply => simp [ValVis_aux] at h_meta_d1
                        obtain ⟨psb, bdyb, cenvb, h_eq⟩ := h_vb
                        subst h_eq
                        have h_lvv_inner :
                            ListValVis [op_a, listToVal args_a] [op_b, listToVal args_b]
                              s_a.heap s_b.heap :=
                          ⟨h_vv_op, ValVis_listToVal h_lvv, trivial⟩
                        have hv_inner_a : ListValValid [op_a, listToVal args_a] s_a.heap :=
                          ⟨hv_opa, ValValid_listToVal hv_argsa, trivial⟩
                        have hv_inner_b : ListValValid [op_b, listToVal args_b] s_b.heap :=
                          ⟨hv_opb, ValValid_listToVal hv_argsb, trivial⟩
                        obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩ :=
                          ih_applyDirect ptable (.closure psa bdya cenva)
                            (.closure psb bdyb cenvb)
                            [op_a, listToVal args_a] [op_b, listToVal args_b]
                            metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_v h_lvv_inner h_meta
                            hv_va hv_vb hv_inner_a hv_inner_b h_eval
                        refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                                h_meta', hv_ra, hv_rb⟩
                        simp [applyVia, hl, hp_b, h_eval_b]
      · -- applyDirect (k+1)
        intro ptable op_a op_b args_a args_b metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_op
              h_lvv h_meta hv_opa hv_opb hv_argsa hv_argsb h_eval
        -- Case-analyze on op_a; ValVis_aux 1 forces op_b's constructor to match.
        have h_vv1 : ValVis_aux 1 op_a op_b s_a.heap s_b.heap := h_vv_op 1
        cases op_a with
        | num n =>
            -- applyDirect on .num returns none → contradiction.
            simp [applyDirect] at h_eval
        | bool b =>
            simp [applyDirect] at h_eval
        | nilV =>
            simp [applyDirect] at h_eval
        | sym s =>
            simp [applyDirect] at h_eval
        | cons xa ya =>
            simp [applyDirect] at h_eval
        | builtinBaseApply =>
            -- v_b is also .builtinBaseApply (forced by ValVis_aux 1).
            have h_opb : op_b = .builtinBaseApply := by
              cases op_b with
              | builtinBaseApply => rfl
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
            subst h_opb
            -- applyDirect builtinBaseApply: destructure args = [actualOp, operandsList].
            simp only [applyDirect] at h_eval
            -- args_a must be exactly [actualOp_a, operandsList_a]; ListValVis forces
            -- args_b to have the same length, so it's [actualOp_b, operandsList_b].
            match args_a, args_b, h_lvv, hv_argsa, hv_argsb with
            | [], _, _, _, _ => simp at h_eval
            | _ :: [], _, _, _, _ => simp at h_eval
            | _ :: _ :: _ :: _, _, _, _, _ => simp at h_eval
            | [actualOp_a, operandsList_a], [], h_lvv', _, _ => exact h_lvv'.elim
            | [actualOp_a, operandsList_a], [_], h_lvv', _, _ =>
                exact h_lvv'.2.elim
            | [actualOp_a, operandsList_a], _ :: _ :: _ :: _, h_lvv', _, _ =>
                exact h_lvv'.2.2.elim
            | [actualOp_a, operandsList_a], [actualOp_b, operandsList_b],
                ⟨h_vv_actual, h_vv_olist, _⟩, ⟨hv_actual_a, hv_olist_a, _⟩,
                ⟨hv_actual_b, hv_olist_b, _⟩ =>
                simp only at h_eval
                cases hl_a : valToList operandsList_a with
                | none => rw [hl_a] at h_eval; simp at h_eval
                | some operands_a =>
                    rw [hl_a] at h_eval
                    simp only at h_eval
                    -- valToList agrees on bisimilar operandsList values.
                    -- Lift this fact via a helper-style induction on operands_a.
                    have h_vol_b : ∃ operands_b,
                        valToList operandsList_b = some operands_b ∧
                        ListValVis operands_a operands_b s_a.heap s_b.heap ∧
                        ListValValid operands_a s_a.heap ∧
                        ListValValid operands_b s_b.heap :=
                      valToList_bisim operands_a operandsList_a operandsList_b
                        s_a.heap s_b.heap hl_a h_vv_olist hv_olist_a hv_olist_b
                    obtain ⟨operands_b, hl_b, h_lvv_ops, hv_ops_a, hv_ops_b⟩ := h_vol_b
                    -- Now apply ih_applyDirect on (actualOp, operands).
                    obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx', h_he',
                            h_meta', hv_ra, hv_rb⟩ :=
                      ih_applyDirect ptable actualOp_a actualOp_b operands_a operands_b
                        metaEnv s_a s_b r_a s_a' hresp_pt h_ctx h_vv_actual h_lvv_ops h_meta
                        hv_actual_a hv_actual_b hv_ops_a hv_ops_b h_eval
                    refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx', h_he',
                            h_meta', hv_ra, hv_rb⟩
                    simp only [applyDirect, hl_b, h_eval_b]
        | prim name =>
            -- op_b must also be .prim name (forced by ValVis_aux 1).
            have h_opb : op_b = .prim name := by
              cases op_b with
              | prim n' =>
                  have : name = n' := by simp [ValVis_aux] at h_vv1; exact h_vv1
                  subst this; rfl
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
            subst h_opb
            -- applyDirect on .prim returns applyPrim name args, state unchanged.
            simp only [applyDirect] at h_eval
            cases hp_a : applyPrim name args_a with
            | none => rw [hp_a] at h_eval; simp at h_eval
            | some v_a' =>
                rw [hp_a] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                obtain ⟨r_b, hp_b, h_vv_r, hv_ra, hv_rb⟩ :=
                  applyPrim_bisim name args_a args_b s_a.heap s_b.heap
                    h_lvv hv_argsa hv_argsb v_a' hp_a
                refine ⟨r_b, s_b, ?_, h_vv_r, h_ctx,
                        HeapEvolution.refl _ _, h_meta, hv_ra, hv_rb⟩
                simp only [applyDirect, hp_b]
        | closure ps body cenv =>
            -- op_b must also be a .closure with the same ps, body, and a
            -- bisim-related cenv (forced by `ValVis_aux 1`).
            have h_opb : ∃ cenv_b, op_b = .closure ps body cenv_b ∧
                cenv = cenv_b ∧
                EnvVis cenv cenv_b s_a.heap s_b.heap := by
              cases op_b with
              | closure ps_b body_b cenv_b =>
                  obtain ⟨hps, hbody, hcenv, henv⟩ :=
                    closure_ValVis_imp_cenv_EnvVis h_vv_op
                  subst hps; subst hbody
                  exact ⟨cenv_b, rfl, hcenv, henv⟩
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
            obtain ⟨cenv_b, h_eq, h_cenv_eq, h_env_cenv⟩ := h_opb
            subst h_eq
            -- ValValid on closures unfolds to EnvValid on cenvs.
            have hev_cenv_a : EnvValid cenv s_a.heap := hv_opa
            have hev_cenv_b : EnvValid cenv_b s_b.heap := hv_opb
            -- Now applyDirect on closure: length check, alloc, eval body.
            simp only [applyDirect] at h_eval
            -- Length check on a-side must succeed (else h_eval = none → contradiction).
            by_cases hlen : ps.length = args_a.length
            · -- Length matches on a-side. By ListValVis, args_b has same length too.
              have hlen_b : ps.length = args_b.length := by
                rw [hlen]; exact ListValVis.length_eq h_lvv
              -- Reduce the if in h_eval (length check passes).
              have hne_a : (ps.length != args_a.length) = false := by
                simp [hlen]
              rw [hne_a] at h_eval
              simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
              -- Now h_eval is the eval of body in the alloc'd state.
              -- Apply alloc_chain_bisim to get post-alloc invariants.
              have hlen_a' : args_a.length = ps.length := hlen.symm
              have hlen_b' : args_b.length = ps.length := hlen_b.symm
              obtain ⟨hh_a', hh_b', hev_a', hev_b', h_env_alloc, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
                alloc_chain_bisim args_a args_b ps cenv cenv_b s_a.heap s_b.heap
                  hlen_a' hlen_b' h_lvv hv_argsa hv_argsb
                  h_ctx.hv_a h_ctx.hv_b hev_cenv_a hev_cenv_b h_env_cenv
              -- Lift EnvVis metaEnv metaEnv to alloc'd heaps.
              have h_meta_alloc : EnvVis metaEnv metaEnv
                  (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).1
                  (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).1 := by
                rw [hex_a, hex_b]
                exact EnvVis_extends metaEnv metaEnv s_a.heap s_b.heap ext_a ext_b
                  h_ctx.hv_a h_ctx.hv_b h_ctx.em_a h_ctx.em_b h_meta
              -- EnvValid metaEnv on alloc'd heaps.
              have hem_a' : EnvValid metaEnv
                  (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).1 :=
                EnvValid.heap_extends h_ctx.em_a ⟨ext_a, hex_a⟩
              have hem_b' : EnvValid metaEnv
                  (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).1 :=
                EnvValid.heap_extends h_ctx.em_b ⟨ext_b, hex_b⟩
              -- Construct WFCtx for the body call.
              -- The two foldl-extended envs match cross-side: cenv = cenv_b
              -- (from closure ValVis), heap_len_eq from h_ctx, args same length.
              -- Use the helper `allocStep_chain_aligned`.
              have h_args_len : args_a.length = args_b.length :=
                ListValVis.length_eq h_lvv
              obtain ⟨h_alloc_env_eq', h_alloc_len_eq'⟩ :=
                allocStep_chain_aligned args_a args_b ps s_a.heap s_b.heap cenv_b
                  h_ctx.heap_len_eq h_args_len
              have h_alloc_env_eq :
                  ((args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).2 : Env)
                    = (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).2 := by
                rw [h_cenv_eq]; exact h_alloc_env_eq'
              have h_alloc_len_eq :
                  (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).1.length =
                    (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).1.length := by
                rw [h_cenv_eq]; exact h_alloc_len_eq'
              have h_ctx_alloc :
                  WFCtx
                    (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).2
                    (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).2
                    metaEnv
                    { s_a with heap := (args_a.zip ps |>.foldl allocStep
                        (s_a.heap, cenv)).1 }
                    { s_b with heap := (args_b.zip ps |>.foldl allocStep
                        (s_b.heap, cenv_b)).1 } :=
                ⟨h_ctx.state_ext, hh_a', hh_b', hev_a', hev_b', hem_a', hem_b',
                 h_ctx.policy_resp, h_alloc_env_eq, h_alloc_len_eq⟩
              -- Now apply ih_eval on body.
              obtain ⟨r_b, s_b', h_eval_b, h_vv_r, h_ctx_body, h_he_body,
                      _h_env_body, h_meta_body, hv_ra, hv_rb⟩ :=
                ih_eval ptable body
                  (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).2
                  (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).2
                  metaEnv
                  { s_a with heap := (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).1 }
                  { s_b with heap := (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).1 }
                  r_a s_a'
                  hresp_pt h_ctx_alloc h_env_alloc h_meta_alloc h_eval
              -- Build heap-evolution chain (alloc step + body step).
              have h_he_alloc :
                  HeapEvolution s_a s_b
                    { s_a with heap := (args_a.zip ps |>.foldl allocStep (s_a.heap, cenv)).1 }
                    { s_b with heap := (args_b.zip ps |>.foldl allocStep (s_b.heap, cenv_b)).1 } :=
                HeapEvolution.from_heapExt h_ctx.hv_a h_ctx.hv_b ⟨ext_a, hex_a⟩ ⟨ext_b, hex_b⟩
              have h_he_chain : HeapEvolution s_a s_b s_a' s_b' :=
                HeapEvolution.trans h_he_alloc h_he_body
              -- Output WFCtx for metaEnv-only env (since this is applyDirect framing).
              have h_ctx_out : WFCtx metaEnv metaEnv metaEnv s_a' s_b' :=
                ⟨h_ctx_body.state_ext, h_ctx_body.hv_a, h_ctx_body.hv_b,
                 h_ctx_body.em_a, h_ctx_body.em_b, h_ctx_body.em_a, h_ctx_body.em_b,
                 h_ctx_body.policy_resp, rfl, h_ctx_body.heap_len_eq⟩
              refine ⟨r_b, s_b', ?_, h_vv_r, h_ctx_out, h_he_chain,
                      h_meta_body, hv_ra, hv_rb⟩
              -- Goal: applyDirect (k+1) ptable (.closure ps body cenv_b) args_b metaEnv s_b
              --       = some (r_b, s_b')
              simp only [applyDirect]
              have hne_b : (ps.length != args_b.length) = false := by simp [hlen_b]
              rw [hne_b]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact h_eval_b
            · -- Length doesn't match on a-side. applyDirect returns none.
              have hne : (ps.length != args_a.length) = true := by simp [hlen]
              rw [hne] at h_eval
              simp at h_eval

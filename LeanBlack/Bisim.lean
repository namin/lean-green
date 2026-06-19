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

/-! ## Weak depth-indexed bisimulation

    `ValVis_aux_weak` is a sibling relation to `ValVis_aux` with the
    `cenv_a = cenv_b` clause **dropped** from the closure case. It
    relates closures that have the same code and cenvs that look up to
    *bisim*-related cells, without requiring the cenvs themselves to be
    Lean-equal. This is the form needed for prefix-extension reasoning,
    where running the same computation on heaps that differ by an
    inserted prefix produces closures whose cenvs differ in their
    fresh-region indices but agree on cell values.

    The strong form `ValVis_aux` is preserved unchanged for the
    `.set`-framing case (which relies on Lean-equal cenvs to align
    cross-side cell updates). A direct bridge `ValVis → ValVis_weak`
    lifts framing's strong outputs to the weak form when needed by
    behavioral-equivalence claims (CE).
-/

def ValVis_aux_weak : Nat → Val → Val → Heap → Heap → Prop
  | 0, _, _, _, _ => True
  | _ + 1, .num a,            .num b,            _,  _   => a = b
  | _ + 1, .bool a,           .bool b,           _,  _   => a = b
  | _ + 1, .nilV,             .nilV,             _,  _   => True
  | _ + 1, .sym a,            .sym b,            _,  _   => a = b
  | _ + 1, .prim a,           .prim b,           _,  _   => a = b
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _,  _   => True
  | n + 1, .cons x_a y_a,     .cons x_b y_b,     h_a, h_b =>
      ValVis_aux_weak n x_a x_b h_a h_b ∧ ValVis_aux_weak n y_a y_b h_a h_b
  | n + 1, .closure ps_a body_a cenv_a,
           .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ body_a = body_b ∧
      (∀ x, match cenv_a.lookup x, cenv_b.lookup x with
            | none, none => True
            | some i_a, some i_b =>
                match h_a[i_a]?, h_b[i_b]? with
                | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                | _, _ => False
            | _, _ => False)
  | _ + 1, _, _, _, _ => False

/-- Weak env bisim: same shape as `EnvVis_aux` but consumes
    `ValVis_aux_weak` on cell values (so closures stored in cells need
    only be weakly bisim-related). -/
def EnvVis_aux_weak (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ x, match env_a.lookup x, env_b.lookup x with
       | none, none => True
       | some i_a, some i_b =>
           match h_a[i_a]?, h_b[i_b]? with
           | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
           | _, _ => False
       | _, _ => False

def ValVis_weak (v_a v_b : Val) (h_a h_b : Heap) : Prop :=
  ∀ n, ValVis_aux_weak n v_a v_b h_a h_b

def EnvVis_weak (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ n, EnvVis_aux_weak n env_a env_b h_a h_b

/-- The closure case of `ValVis_aux_weak`: same code, with cenvs
    pointwise-bisim through their shared name set (no Lean-equality
    requirement). -/
theorem ValVis_aux_weak_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVis_aux_weak (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ body_a = body_b ∧
       EnvVis_aux_weak n cenv_a cenv_b h_a h_b) := by
  simp [ValVis_aux_weak, EnvVis_aux_weak]

/-! ### Bridge: strong → weak

    `ValVis_aux n` is strictly stronger than `ValVis_aux_weak n` — it
    adds `cenv_a = cenv_b` on the closure case, but otherwise matches
    pointwise. The bridge is direct structural induction on `n`.
-/

theorem ValVis_aux_to_weak : ∀ (n : Nat) (v_a v_b : Val) (h_a h_b : Heap),
    ValVis_aux n v_a v_b h_a h_b → ValVis_aux_weak n v_a v_b h_a h_b
  | 0, _, _, _, _, _ => trivial
  | n + 1, .num _,            .num _,            _, _, h => h
  | n + 1, .bool _,           .bool _,           _, _, h => h
  | n + 1, .nilV,             .nilV,             _, _, h => h
  | n + 1, .sym _,            .sym _,            _, _, h => h
  | n + 1, .prim _,           .prim _,           _, _, h => h
  | n + 1, .builtinBaseApply, .builtinBaseApply, _, _, h => h
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, h =>
      ⟨ValVis_aux_to_weak n x_a x_b h_a h_b h.1,
       ValVis_aux_to_weak n y_a y_b h_a h_b h.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b, h_a, h_b, h => by
      obtain ⟨hps, hbody, _hcenv, henv⟩ := h
      show ps_a = ps_b ∧ body_a = body_b ∧ _
      refine ⟨hps, hbody, ?_⟩
      intro x
      have hx := henv x
      cases ha : cenv_a.lookup x with
      | none =>
          cases hb : cenv_b.lookup x with
          | none => trivial
          | some i_b => rw [ha, hb] at hx; simp at hx
      | some i_a =>
          cases hb : cenv_b.lookup x with
          | none => rw [ha, hb] at hx; simp at hx
          | some i_b =>
              rw [ha, hb] at hx
              simp only at hx
              cases hpa : h_a[i_a]? with
              | none =>
                  rw [hpa] at hx
                  cases hpb : h_b[i_b]? <;> rw [hpb] at hx <;> exact hx.elim
              | some w_a =>
                  cases hpb : h_b[i_b]? with
                  | none => rw [hpa, hpb] at hx; exact hx.elim
                  | some w_b =>
                      rw [hpa, hpb] at hx
                      show match h_a[i_a]?, h_b[i_b]? with
                           | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                           | _, _ => False
                      rw [hpa, hpb]
                      exact ValVis_aux_to_weak n w_a w_b h_a h_b hx
  -- Mismatched constructor cases: ValVis_aux is False, contradicts h.
  | n + 1, .num _, .bool _, _, _, h => h.elim
  | n + 1, .num _, .nilV, _, _, h => h.elim
  | n + 1, .num _, .sym _, _, _, h => h.elim
  | n + 1, .num _, .prim _, _, _, h => h.elim
  | n + 1, .num _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .num _, .cons _ _, _, _, h => h.elim
  | n + 1, .num _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .bool _, .num _, _, _, h => h.elim
  | n + 1, .bool _, .nilV, _, _, h => h.elim
  | n + 1, .bool _, .sym _, _, _, h => h.elim
  | n + 1, .bool _, .prim _, _, _, h => h.elim
  | n + 1, .bool _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .bool _, .cons _ _, _, _, h => h.elim
  | n + 1, .bool _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .nilV, .num _, _, _, h => h.elim
  | n + 1, .nilV, .bool _, _, _, h => h.elim
  | n + 1, .nilV, .sym _, _, _, h => h.elim
  | n + 1, .nilV, .prim _, _, _, h => h.elim
  | n + 1, .nilV, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .nilV, .cons _ _, _, _, h => h.elim
  | n + 1, .nilV, .closure _ _ _, _, _, h => h.elim
  | n + 1, .sym _, .num _, _, _, h => h.elim
  | n + 1, .sym _, .bool _, _, _, h => h.elim
  | n + 1, .sym _, .nilV, _, _, h => h.elim
  | n + 1, .sym _, .prim _, _, _, h => h.elim
  | n + 1, .sym _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .sym _, .cons _ _, _, _, h => h.elim
  | n + 1, .sym _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .prim _, .num _, _, _, h => h.elim
  | n + 1, .prim _, .bool _, _, _, h => h.elim
  | n + 1, .prim _, .nilV, _, _, h => h.elim
  | n + 1, .prim _, .sym _, _, _, h => h.elim
  | n + 1, .prim _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .prim _, .cons _ _, _, _, h => h.elim
  | n + 1, .prim _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .num _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .bool _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .nilV, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .sym _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .prim _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .cons _ _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .closure _ _ _, _, _, h => h.elim
  | n + 1, .cons _ _, .num _, _, _, h => h.elim
  | n + 1, .cons _ _, .bool _, _, _, h => h.elim
  | n + 1, .cons _ _, .nilV, _, _, h => h.elim
  | n + 1, .cons _ _, .sym _, _, _, h => h.elim
  | n + 1, .cons _ _, .prim _, _, _, h => h.elim
  | n + 1, .cons _ _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .cons _ _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .num _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .bool _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .nilV, _, _, h => h.elim
  | n + 1, .closure _ _ _, .sym _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .prim _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .closure _ _ _, .cons _ _, _, _, h => h.elim

theorem EnvVis_aux_to_weak (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) :
    EnvVis_aux n env_a env_b h_a h_b → EnvVis_aux_weak n env_a env_b h_a h_b := by
  intro h x
  have hx := h x
  cases ha : env_a.lookup x with
  | none =>
      cases hb : env_b.lookup x with
      | none => trivial
      | some _ => rw [ha, hb] at hx; simp at hx
  | some i_a =>
      cases hb : env_b.lookup x with
      | none => rw [ha, hb] at hx; simp at hx
      | some i_b =>
          rw [ha, hb] at hx
          simp only at hx
          cases hpa : h_a[i_a]? with
          | none =>
              rw [hpa] at hx
              cases hpb : h_b[i_b]? <;> rw [hpb] at hx <;> exact hx.elim
          | some w_a =>
              cases hpb : h_b[i_b]? with
              | none => rw [hpa, hpb] at hx; exact hx.elim
              | some w_b =>
                  rw [hpa, hpb] at hx
                  show match h_a[i_a]?, h_b[i_b]? with
                       | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                       | _, _ => False
                  rw [hpa, hpb]
                  exact ValVis_aux_to_weak n w_a w_b h_a h_b hx

theorem ValVis_to_weak {v_a v_b : Val} {h_a h_b : Heap} :
    ValVis v_a v_b h_a h_b → ValVis_weak v_a v_b h_a h_b :=
  fun h n => ValVis_aux_to_weak n v_a v_b h_a h_b (h n)

theorem EnvVis_to_weak {env_a env_b : Env} {h_a h_b : Heap} :
    EnvVis env_a env_b h_a h_b → EnvVis_weak env_a env_b h_a h_b :=
  fun h n => EnvVis_aux_to_weak n env_a env_b h_a h_b (h n)

/-- Pointwise weak list bisim. -/
def ListValVis_weak : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVis_weak x y h_a h_b ∧ ListValVis_weak xs ys h_a h_b
  | _,       _,       _,   _   => False

theorem ListValVis_weak.length_eq : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis_weak xs ys h_a h_b → xs.length = ys.length
  | [],      [],      _, _, _ => rfl
  | [],      _ :: _,  _, _, h => absurd h (by simp [ListValVis_weak])
  | _ :: _,  [],      _, _, h => absurd h (by simp [ListValVis_weak])
  | _ :: xs, _ :: ys, _, _, ⟨_, h_tail⟩ => by
      simp [List.length_cons, ListValVis_weak.length_eq h_tail]

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

/-- Out-of-bounds update is a no-op. -/
theorem Heap.update_oob : ∀ (h : Heap) (idx : Nat) (v : Val),
    h.length ≤ idx → Heap.update h idx v = h
  | [],       _,     _, _    => rfl
  | _ :: _,   0,     _, h_le => by simp at h_le
  | _ :: t,   n + 1, v, h_le => by
      simp only [Heap.update]
      simp only [List.length_cons] at h_le
      exact congrArg _ (Heap.update_oob t n v (Nat.le_of_succ_le_succ h_le))

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

/-! ## Weak-bisim heap-extension lemmas

    Weak versions of the strong heap-extension lemmas above. The closure
    case loses the `cenv_a = cenv_b` clause but keeps the cell-pointwise
    bisim, which is preserved by extension via the standard nested
    induction. The non-closure cases are identical to the strong case
    (modulo the type signature), so these largely mirror
    `ValVis_aux_extends` / `EnvVis_aux_extends`. -/

mutual

theorem ValVis_aux_weak_extends : ∀ (n : Nat) (v_a v_b : Val)
    (h_a h_b ext_a ext_b : Heap),
    HeapValid h_a → HeapValid h_b →
    ValValid v_a h_a → ValValid v_b h_b →
    ValVis_aux_weak n v_a v_b h_a h_b →
    ValVis_aux_weak n v_a v_b (h_a ++ ext_a) (h_b ++ ext_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, ext_a, ext_b,
      hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨ValVis_aux_weak_extends n x_a x_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.1 hv_b.1 h_vis.1,
       ValVis_aux_weak_extends n y_a y_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.2 hv_b.2 h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, ext_a, ext_b, hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨h_vis.1, h_vis.2.1,
       EnvVis_aux_weak_extends n cenv_a cenv_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a hv_b h_vis.2.2⟩
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

theorem EnvVis_aux_weak_extends (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap),
      HeapValid h_a → HeapValid h_b →
      EnvValid env_a h_a → EnvValid env_b h_b →
      EnvVis_aux_weak n env_a env_b h_a h_b →
      EnvVis_aux_weak n env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b h_vis x
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => simp [hl_a, hl_b, EnvVis_aux_weak]
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
          simp only [hl_a, hl_b]
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
                  exact ValVis_aux_weak_extends n v_a v_b h_a h_b ext_a ext_b
                    hh_a hh_b hv_va hv_vb h_x

end

/-- Universal-depth weak val-vis preserved under heap extension. -/
theorem ValVis_weak_extends (v_a v_b : Val) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : ValValid v_a h_a) (hv_b : ValValid v_b h_b)
    (h_vis : ValVis_weak v_a v_b h_a h_b) :
    ValVis_weak v_a v_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact ValVis_aux_weak_extends n v_a v_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

theorem EnvVis_weak_extends (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : EnvValid env_a h_a) (hv_b : EnvValid env_b h_b)
    (h_vis : EnvVis_weak env_a env_b h_a h_b) :
    EnvVis_weak env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact EnvVis_aux_weak_extends n env_a env_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

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
    -- new values bisim-related at the updated heap pair, at depths < n.
    -- This is the STRICTLY BOUNDED form (was `∀ k, ...` universal): the
    -- closure case only needs h_vis_new at depths < n (used at depth
    -- n-1 in `EnvVis_aux_update`, and recursively at depths < n-1).
    -- The strict bound enables a depth-induction self-update lemma
    -- where the caller constructs h_vis_new from IH at strictly
    -- smaller depths (without needing the current depth's result).
    (∀ k, k < n → ValVis_aux k newVal_a newVal_b
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
      -- Recursive .cons calls at depth n: weaken from `< n+1` to `< n`.
      -- (k < n implies k < n+1 by Nat.lt_succ_of_lt.)
      ⟨ValVis_aux_update n x_a x_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.1 hv_b.1
          (fun k h_lt => h_vis_new k (Nat.lt_succ_of_lt h_lt))
          hv_new_a hv_new_b h_vis.1,
       ValVis_aux_update n y_a y_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.2 hv_b.2
          (fun k h_lt => h_vis_new k (Nat.lt_succ_of_lt h_lt))
          hv_new_a hv_new_b h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, idx, newVal_a, newVal_b,
      hh_a, hh_b, hlen, hv_a, hv_b, h_vis_new, hv_new_a, hv_new_b, h_vis =>
      -- ValValid on closure unfolds to EnvValid on cenv. Cenv equality
      -- (`h_vis.2.2.1`) is what feeds `EnvVis_aux_update`'s `env_eq`.
      -- Outer bound is `< n+1` (= `≤ n`); EnvVis_aux_update at depth n
      -- takes bound `≤ n`. Convert via `Nat.lt_succ_iff.mp`.
      ⟨h_vis.1, h_vis.2.1, h_vis.2.2.1,
       EnvVis_aux_update n cenv_a cenv_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a hv_b h_vis.2.2.1
          (fun k h_le => h_vis_new k (Nat.lt_succ_of_le h_le))
          hv_new_a hv_new_b h_vis.2.2.2⟩
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
      (∀ k, k ≤ n → ValVis_aux k newVal_a newVal_b
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
        exact h_vis_new n (Nat.le_refl n)
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
                -- ValVis_aux_update at depth n needs bound `< n`. We have
                -- `≤ n` (EnvVis's outer bound). Weaken: k < n → k ≤ n.
                exact ValVis_aux_update n v_a v_b h_a h_b idx
                  newVal_a newVal_b hh_a hh_b hlen hv_va hv_vb
                  (fun k h_lt => h_vis_new k (Nat.le_of_lt h_lt))
                  hv_new_a hv_new_b h_x

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

/-- `ValVis_weak` on `.bool false` is two-sided. -/
theorem ValVis_weak_bool_false_iff (cv_a cv_b : Val) (h_a h_b : Heap)
    (h_vv : ValVis_weak cv_a cv_b h_a h_b) :
    cv_a = .bool false ↔ cv_b = .bool false := by
  constructor
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_b with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux_weak] at h1
    | num _            => simp [ValVis_aux_weak] at h1
    | nilV             => simp [ValVis_aux_weak] at h1
    | cons _ _         => simp [ValVis_aux_weak] at h1
    | sym _            => simp [ValVis_aux_weak] at h1
    | closure _ _ _    => simp [ValVis_aux_weak] at h1
    | prim _           => simp [ValVis_aux_weak] at h1
    | builtinBaseApply => simp [ValVis_aux_weak] at h1
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_a with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux_weak] at h1
    | num _            => simp [ValVis_aux_weak] at h1
    | nilV             => simp [ValVis_aux_weak] at h1
    | cons _ _         => simp [ValVis_aux_weak] at h1
    | sym _            => simp [ValVis_aux_weak] at h1
    | closure _ _ _    => simp [ValVis_aux_weak] at h1
    | prim _           => simp [ValVis_aux_weak] at h1
    | builtinBaseApply => simp [ValVis_aux_weak] at h1

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

theorem ListValVis_weak_extends : ∀ {xs ys : List Val} {h_a h_b ext_a ext_b : Heap},
    HeapValid h_a → HeapValid h_b →
    ListValValid xs h_a → ListValValid ys h_b →
    ListValVis_weak xs ys h_a h_b →
    ListValVis_weak xs ys (h_a ++ ext_a) (h_b ++ ext_b)
  | [],      [],      _, _, _, _, _, _, _, _, _ => trivial
  | [],      _ :: _,  _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  [],      _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, _, _, hh_a, hh_b, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_weak_extends _ _ _ _ _ _ hh_a hh_b hv_a.1 hv_b.1 h_head,
       ListValVis_weak_extends hh_a hh_b hv_a.2 hv_b.2 h_tail⟩

theorem ListValVis_to_weak : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b → ListValVis_weak xs ys h_a h_b
  | [],      [],      _, _, _ => trivial
  | [],      _ :: _,  _, _, h => h.elim
  | _ :: _,  [],      _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_to_weak h_head, ListValVis_to_weak h_tail⟩

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
  cases h

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

/-! ## ValVis collapses to Val equality

    Under the strengthened `ValVis_aux` on closures (which now
    requires `cenv_a = cenv_b` structurally), universal-depth
    bisimulation between two values implies they are *equal* as
    Lean terms. Used by the `PolicyRespectsBisim` proofs for
    policies that pattern-match on `Val` structure (where bisim-
    related inputs need to give the same pattern result). -/
theorem bisim_imp_eq : ∀ (v1 v2 : Val) (h1 h2 : Heap),
    ValVis v1 v2 h1 h2 → v1 = v2
  | .num _,            v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .bool _,           v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .nilV,             v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first | rfl | (simp [ValVis_aux] at h)
  | .sym _,            v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .prim _,           v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .builtinBaseApply, v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first | rfl | (simp [ValVis_aux] at h)
  | .cons x_a y_a,     v2, _, _, h_vis => by
      have h1 := h_vis 1
      cases v2 with
      | cons x_b y_b =>
          -- ValVis at depth k+1 on .cons: ValVis_aux k on each component.
          have h_x : ValVis x_a x_b _ _ := fun k => (h_vis (k + 1)).1
          have h_y : ValVis y_a y_b _ _ := fun k => (h_vis (k + 1)).2
          have ex := bisim_imp_eq x_a x_b _ _ h_x
          have ey := bisim_imp_eq y_a y_b _ _ h_y
          rw [ex, ey]
      | num _ => simp [ValVis_aux] at h1
      | bool _ => simp [ValVis_aux] at h1
      | nilV => simp [ValVis_aux] at h1
      | sym _ => simp [ValVis_aux] at h1
      | closure _ _ _ => simp [ValVis_aux] at h1
      | prim _ => simp [ValVis_aux] at h1
      | builtinBaseApply => simp [ValVis_aux] at h1
  | .closure ps body cenv, v2, _, _, h_vis => by
      have h1 := h_vis 1
      cases v2 with
      | closure ps_b body_b cenv_b =>
          -- ValVis_aux 1 on closures gives ps_eq, body_eq, cenv_eq.
          obtain ⟨h_ps, h_body, h_cenv, _⟩ := h1
          rw [h_ps, h_body, h_cenv]
      | num _ => simp [ValVis_aux] at h1
      | bool _ => simp [ValVis_aux] at h1
      | nilV => simp [ValVis_aux] at h1
      | sym _ => simp [ValVis_aux] at h1
      | cons _ _ => simp [ValVis_aux] at h1
      | prim _ => simp [ValVis_aux] at h1
      | builtinBaseApply => simp [ValVis_aux] at h1

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
                    -- Validity at NEW heaps (length-preserved by Heap.update).
                    have hv_va_new0 :
                        ValValid v_a (s_a_inner.heap.update idx v_a) :=
                      ValValid.length_mono v_a hv_va
                        (Nat.le_of_eq (Heap.update_length _ _ _).symm)
                    have hv_vb_new0 :
                        ValValid v_b (s_b_inner.heap.update idx v_b) :=
                      ValValid.length_mono v_b hv_vb
                        (Nat.le_of_eq (Heap.update_length _ _ _).symm)
                    -- Self-update preserves universal-depth bisim.
                    -- Prove the strengthened form `∀ k ≤ K, ValVis_aux k`
                    -- by induction on K, then specialize to extract at
                    -- each k. The strengthening ensures that at K=N+1,
                    -- the IH at K=N already provides bisim at all
                    -- depths ≤ N, which is exactly what
                    -- `ValVis_aux_update` at depth N+1 (bound `< N+1`)
                    -- needs as its precondition.
                    have h_vis_v_at_new_strong :
                        ∀ K k, k ≤ K → ValVis_aux k v_a v_b
                              (s_a_inner.heap.update idx v_a)
                              (s_b_inner.heap.update idx v_b) := by
                      intro K
                      induction K with
                      | zero =>
                          intro k h_le
                          have : k = 0 := Nat.le_zero.mp h_le
                          subst this
                          trivial
                      | succ N ih =>
                          intro k h_le
                          by_cases h_le_N : k ≤ N
                          · exact ih k h_le_N
                          · -- k > N and k ≤ N+1 → k = N+1.
                            have h_eq : k = N + 1 := by omega
                            subst h_eq
                            -- Apply ValVis_aux_update at depth N+1.
                            apply ValVis_aux_update (N+1) v_a v_b
                              s_a_inner.heap s_b_inner.heap idx v_a v_b
                              h_ctx_inner.hv_a h_ctx_inner.hv_b
                              h_ctx_inner.heap_len_eq hv_va hv_vb
                              ?_ hv_va_new0 hv_vb_new0 (h_vv_v (N+1))
                            -- Precondition: ∀ k' < N+1, ValVis_aux k' at NEW.
                            -- = ∀ k' ≤ N, ValVis_aux k' at NEW. = ih.
                            intro k' h_lt
                            exact ih k' (Nat.le_of_lt_succ h_lt)
                    have h_vis_v_at_new :
                        ∀ k, ValVis_aux k v_a v_b
                              (s_a_inner.heap.update idx v_a)
                              (s_b_inner.heap.update idx v_b) := by
                      intro k
                      exact h_vis_v_at_new_strong k k (Nat.le_refl k)
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
                          h_env_eq' (fun k _ => h_vis_v_at_new k)
                          hv_va_new hv_vb_new h_env_vis
                      · intro nV v_x v_y hv_x hv_y h_v_vis
                        -- Apply ValVis_aux_update at depth nV on (v_x, v_y).
                        exact ValVis_aux_update nV v_x v_y
                          s_a_inner.heap s_b_inner.heap idx v_a v_b
                          h_ctx_inner.hv_a h_ctx_inner.hv_b
                          h_ctx_inner.heap_len_eq hv_x hv_y
                          (fun k _ => h_vis_v_at_new k)
                          hv_va_new hv_vb_new h_v_vis
                    -- Now case-analyze on isMetaMutation x env_a metaEnv.
                    by_cases h_meta_mut : isMetaMutation x env_a metaEnv = true
                    · -- META MUTATION CASE.
                      have h_meta_mut_b : isMetaMutation x env_b metaEnv = true := by
                        unfold isMetaMutation at h_meta_mut ⊢
                        rw [hl] at h_meta_mut; rw [hl_b]
                        exact h_meta_mut
                      -- 1. Derive `metaEnv.lookup x = some idx` from
                      --    `isMetaMutation x env_a metaEnv = true`.
                      have h_meta_lookup : metaEnv.lookup x = some idx := by
                        have h_mm := h_meta_mut
                        unfold isMetaMutation at h_mm
                        rw [hl] at h_mm
                        cases h_ml : metaEnv.lookup x with
                        | none => rw [h_ml] at h_mm; simp at h_mm
                        | some i_meta =>
                            rw [h_ml] at h_mm
                            have h_eq : idx = i_meta := by simpa using h_mm
                            -- Goal after `cases` rewrote the lookup:
                            -- `some i_meta = some idx`. Use h_eq.
                            rw [← h_eq]
                      simp only [h_meta_mut] at h_eval
                      cases hp_a : s_a_inner.heap[idx]? with
                      | none => rw [hp_a] at h_eval; simp at h_eval
                      | some oldVal_a =>
                          rw [hp_a] at h_eval
                          simp only at h_eval
                          -- 2. Get oldVal_b on side B at idx via EnvVis on metaEnv.
                          have h_meta_inner_x_1 := h_meta_inner 1 x
                          rw [h_meta_lookup] at h_meta_inner_x_1
                          simp only at h_meta_inner_x_1
                          rw [hp_a] at h_meta_inner_x_1
                          cases hp_b : s_b_inner.heap[idx]? with
                          | none =>
                              rw [hp_b] at h_meta_inner_x_1
                              simp at h_meta_inner_x_1
                          | some oldVal_b =>
                              rw [hp_b] at h_meta_inner_x_1
                              -- Universal-depth ValVis on (oldVal_a, oldVal_b).
                              have h_vv_old : ValVis oldVal_a oldVal_b
                                  s_a_inner.heap s_b_inner.heap := by
                                intro d
                                have h_meta_d := h_meta_inner d x
                                rw [h_meta_lookup] at h_meta_d
                                simp only at h_meta_d
                                rw [hp_a, hp_b] at h_meta_d
                                exact h_meta_d
                              have hv_old_a : ValValid oldVal_a s_a_inner.heap :=
                                h_ctx_inner.hv_a idx oldVal_a hp_a
                              have hv_old_b : ValValid oldVal_b s_b_inner.heap :=
                                h_ctx_inner.hv_b idx oldVal_b hp_b
                              -- 3. Apply policy_resp. The gate is `s_a.policy`
                              -- (frozen at .set start). PolicyRespectsBisim is
                              -- on `s_a.policy` via `h_ctx.policy_resp`.
                              -- env_a = env_b via h_ctx.env_eq, so
                              -- EnvVis env env_b == EnvVis env env (same env).
                              have h_env_inner_eq :
                                  EnvVis env_a env_a s_a_inner.heap s_b_inner.heap := by
                                rw [h_ctx_inner.env_eq] at h_env_inner ⊢
                                exact h_env_inner
                              have h_policy_eq :
                                  s_a.policy
                                    { target := x, heap := s_a_inner.heap,
                                      env := env_a, metaEnv := metaEnv,
                                      index := idx } oldVal_a v_a =
                                  s_a.policy
                                    { target := x, heap := s_b_inner.heap,
                                      env := env_a, metaEnv := metaEnv,
                                      index := idx } oldVal_b v_b :=
                                h_ctx.policy_resp x idx env_a metaEnv
                                  s_a_inner.heap s_b_inner.heap
                                  oldVal_a oldVal_b v_a v_b
                                  h_ctx_inner.hv_a h_ctx_inner.hv_b
                                  h_ctx_inner.ev_a (h_ctx_inner.env_eq ▸ h_ctx_inner.ev_b)
                                  h_ctx_inner.em_a h_ctx_inner.em_b
                                  hv_old_a hv_old_b hv_va hv_vb
                                  h_env_inner_eq
                                  h_meta_inner h_vv_old h_vv_v
                              -- 4. Case on gate decision.
                              by_cases h_gate :
                                  s_a.policy
                                    { target := x, heap := s_a_inner.heap,
                                      env := env_a, metaEnv := metaEnv,
                                      index := idx } oldVal_a v_a = true
                              · -- ADMIT.
                                rw [h_gate] at h_eval
                                simp only [↓reduceIte, Option.some.injEq,
                                           Prod.mk.injEq] at h_eval
                                obtain ⟨h_r, h_s⟩ := h_eval
                                subst h_r; subst h_s
                                -- Side B's gate decision.
                                have h_gate_b :
                                    s_b.policy
                                      { target := x, heap := s_b_inner.heap,
                                        env := env_b, metaEnv := metaEnv,
                                        index := idx } oldVal_b v_b = true := by
                                  rw [← h_ctx.state_ext]
                                  rw [← h_ctx.env_eq]
                                  rw [← h_policy_eq]
                                  exact h_gate
                                -- HeapEvolution chain.
                                have h_he_chain : HeapEvolution s_a s_b
                                    { s_a_inner with
                                        heap := s_a_inner.heap.update idx v_a }
                                    { s_b_inner with
                                        heap := s_b_inner.heap.update idx v_b } :=
                                  HeapEvolution.trans h_he_inner h_he_update
                                -- Output WFCtx (same construction as plain case).
                                have h_len_a_loc : s_a_inner.heap.length =
                                    (s_a_inner.heap.update idx v_a).length :=
                                  (Heap.update_length _ _ _).symm
                                have h_len_b_loc : s_b_inner.heap.length =
                                    (s_b_inner.heap.update idx v_b).length :=
                                  (Heap.update_length _ _ _).symm
                                have h_le_a_loc : s_a_inner.heap.length ≤
                                    (s_a_inner.heap.update idx v_a).length :=
                                  Nat.le_of_eq h_len_a_loc
                                have h_le_b_loc : s_b_inner.heap.length ≤
                                    (s_b_inner.heap.update idx v_b).length :=
                                  Nat.le_of_eq h_len_b_loc
                                have hh_a_new :
                                    HeapValid (s_a_inner.heap.update idx v_a) := by
                                  intro i v hp
                                  by_cases h_ieq : i = idx
                                  · subst h_ieq
                                    rw [Heap.update_get_eq _ _ _
                                        (h_ctx_inner.ev_a x i hl)] at hp
                                    simp only [Option.some.injEq] at hp
                                    subst hp
                                    exact ValValid.length_mono v_a hv_va h_le_a_loc
                                  · rw [Heap.update_get_neq _ _ _ _ h_ieq] at hp
                                    have hv_old := h_ctx_inner.hv_a i v hp
                                    exact ValValid.length_mono v hv_old h_le_a_loc
                                have hh_b_new :
                                    HeapValid (s_b_inner.heap.update idx v_b) := by
                                  intro i v hp
                                  by_cases h_ieq : i = idx
                                  · subst h_ieq
                                    rw [Heap.update_get_eq _ _ _
                                        (h_ctx_inner.ev_b x i hl_b)] at hp
                                    simp only [Option.some.injEq] at hp
                                    subst hp
                                    exact ValValid.length_mono v_b hv_vb h_le_b_loc
                                  · rw [Heap.update_get_neq _ _ _ _ h_ieq] at hp
                                    have hv_old := h_ctx_inner.hv_b i v hp
                                    exact ValValid.length_mono v hv_old h_le_b_loc
                                have h_ctx_out :
                                    WFCtx env_a env_b metaEnv
                                      { s_a_inner with
                                          heap := s_a_inner.heap.update idx v_a }
                                      { s_b_inner with
                                          heap := s_b_inner.heap.update idx v_b } := by
                                  refine ⟨h_ctx_inner.state_ext, hh_a_new, hh_b_new,
                                          ?_, ?_, ?_, ?_, h_ctx_inner.policy_resp,
                                          h_ctx_inner.env_eq, ?_⟩
                                  · exact EnvValid.length_mono h_ctx_inner.ev_a h_le_a_loc
                                  · exact EnvValid.length_mono h_ctx_inner.ev_b h_le_b_loc
                                  · exact EnvValid.length_mono h_ctx_inner.em_a h_le_a_loc
                                  · exact EnvValid.length_mono h_ctx_inner.em_b h_le_b_loc
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
                                        { s_b_inner with
                                            heap := s_b_inner.heap.update idx v_b },
                                        ?_,
                                        (fun d => by cases d with
                                          | zero => trivial
                                          | succ _ => rfl),
                                        h_ctx_out, h_he_chain,
                                        h_env_out, h_meta_out, trivial, trivial⟩
                                simp [eval, h_eval_e_b, hl_b, h_meta_mut_b,
                                      hp_b, h_gate_b]
                              · -- REJECT.
                                have h_gate_false :
                                    s_a.policy
                                      { target := x, heap := s_a_inner.heap,
                                        env := env_a, metaEnv := metaEnv,
                                        index := idx } oldVal_a v_a = false := by
                                  cases h_dec : s_a.policy ⟨x, s_a_inner.heap,
                                    env_a, metaEnv, idx⟩ oldVal_a v_a
                                  · rfl
                                  · exact absurd h_dec h_gate
                                rw [h_gate_false] at h_eval
                                simp only [Bool.false_eq_true, ↓reduceIte,
                                           Option.some.injEq, Prod.mk.injEq] at h_eval
                                obtain ⟨h_r, h_s⟩ := h_eval
                                subst h_r; subst h_s
                                -- Side B's gate decision (= false).
                                have h_gate_b :
                                    s_b.policy
                                      { target := x, heap := s_b_inner.heap,
                                        env := env_b, metaEnv := metaEnv,
                                        index := idx } oldVal_b v_b = false := by
                                  rw [← h_ctx.state_ext, ← h_ctx.env_eq,
                                      ← h_policy_eq]
                                  exact h_gate_false
                                -- State unchanged on both sides; HeapEvolution = h_he_inner.
                                refine ⟨.bool false, s_b_inner, ?_,
                                        (fun d => by cases d with
                                          | zero => trivial
                                          | succ _ => rfl),
                                        h_ctx_inner, h_he_inner, h_env_inner,
                                        h_meta_inner, trivial, trivial⟩
                                simp [eval, h_eval_e_b, hl_b, h_meta_mut_b,
                                      hp_b, h_gate_b]
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

/-! ## Single-side validity preservation

    Specialize `frame` with `env_a = env_b = env`, `s_a = s_b = s` to
    extract single-side validity-preservation facts: `eval`/`evalList`/
    `applyVia`/`applyDirect` preserve `HeapValid`, produce `ValValid`
    results, and preserve `EnvValid` of the active env. -/

private theorem applyDirect_preserves_validity
    {fuel : Nat} {ptable : PolicyTable} (hresp_pt : PolicyTableRespectsBisim ptable)
    {op : Val} {operands : List Val} {metaEnv : Env} {s : RunState}
    (h_heap : HeapValid s.heap) (h_op : ValValid op s.heap)
    (h_operands : ListValValid operands s.heap)
    (h_meta : EnvValid metaEnv s.heap)
    (hresp_init : PolicyRespectsBisim s.policy)
    {r : Val} {s' : RunState}
    (h_app : applyDirect fuel ptable op operands metaEnv s = some (r, s')) :
    HeapValid s'.heap ∧ ValValid r s'.heap ∧ EnvValid metaEnv s'.heap ∧
    s.heap.length ≤ s'.heap.length := by
  obtain ⟨_, _, _, ih_apd⟩ := frame fuel
  have h_ctx : WFCtx metaEnv metaEnv metaEnv s s :=
    WFCtx.refl metaEnv metaEnv s h_heap h_meta h_meta hresp_init
  -- self-self ValVis: use ValVis_aux_self_extend with extras = [].
  have h_op_vis : ValVis op op s.heap s.heap := by
    intro depth
    have := ValVis_aux_self_extend depth op s.heap [] h_heap h_op
    rwa [List.append_nil] at this
  have h_args_vis : ListValVis operands operands s.heap s.heap := by
    have aux : ∀ {ops : List Val}, ListValValid ops s.heap →
        ListValVis ops ops s.heap s.heap := by
      intro ops hv
      induction ops with
      | nil => trivial
      | cons head tail ih =>
          obtain ⟨hv_h, hv_t⟩ := hv
          refine ⟨?_, ih hv_t⟩
          intro depth
          have := ValVis_aux_self_extend depth head s.heap [] h_heap hv_h
          rwa [List.append_nil] at this
    exact aux h_operands
  have h_meta_vis : EnvVis metaEnv metaEnv s.heap s.heap := by
    intro depth
    apply EnvVis_aux_self_of_valid' depth metaEnv s.heap s.heap h_meta h_heap
      ⟨[], by rw [List.append_nil]⟩
    intro v hv
    have := ValVis_aux_self_extend depth v s.heap [] h_heap hv
    rwa [List.append_nil] at this
  obtain ⟨r_b, s_b', h_app_b, _h_vv_r, h_ctx', h_he, _h_meta', hv_ra, _hv_rb⟩ :=
    ih_apd ptable op op operands operands metaEnv s s r s'
      hresp_pt h_ctx h_op_vis h_args_vis h_meta_vis
      h_op h_op h_operands h_operands h_app
  -- By determinism: r_b = r and s_b' = s'.
  have h_eq_pair : (r_b, s_b') = (r, s') := by
    have h_eq := h_app.symm.trans h_app_b
    exact Option.some_inj.mp h_eq.symm
  have h_r : r_b = r := (Prod.mk.injEq _ _ _ _).mp h_eq_pair |>.1
  have h_s : s_b' = s' := (Prod.mk.injEq _ _ _ _).mp h_eq_pair |>.2
  subst h_r; subst h_s
  exact ⟨h_ctx'.hv_a, hv_ra, h_ctx'.em_a, h_he.len_a⟩

/-! ## Functional shift: heap-prefix-insertion as a syntactic operation

    The semantic content of the prefix-extension lemma is
    `applyDirect on s succeeds ⇒ applyDirect on s ++ extras succeeds`.
    Side B's behavior is *functionally determined* by side A's: every
    fresh heap address ≥ `cutoff` (= original heap length) is shifted up
    by `offset` (= `extras.length`). We make this functional structure
    explicit via `shift_idx` / `shift_val` / `shift_env` / `shift_heap`,
    then prove `eval` / `evalList` / `applyVia` / `applyDirect` all
    *commute* with shift. The original lemma falls out as an instance.

    This is much cleaner than relational bisimulation because each case
    becomes a pure-function commutativity check (`Heap.update` commutes
    with shift, `Env.lookup` commutes with shift, `applyPrim` commutes
    with shift on args, etc.) rather than threading bisim invariants. -/

/-- Shift an absolute heap index: indices `< cutoff` are unchanged;
    indices `≥ cutoff` are bumped up by `offset`. -/
def shift_idx (cutoff offset i : Nat) : Nat :=
  if i < cutoff then i else i + offset

mutual
def shift_val (cutoff offset : Nat) : Val → Val
  | .num n              => .num n
  | .bool b             => .bool b
  | .nilV               => .nilV
  | .cons x y           =>
      .cons (shift_val cutoff offset x) (shift_val cutoff offset y)
  | .sym s              => .sym s
  | .prim s             => .prim s
  | .builtinBaseApply   => .builtinBaseApply
  | .closure ps body cenv => .closure ps body (shift_env cutoff offset cenv)

def shift_env (cutoff offset : Nat) : Env → Env
  | .nil               => .nil
  | .cons name idx rest =>
      .cons name (shift_idx cutoff offset idx) (shift_env cutoff offset rest)
end

def shift_listVal (cutoff offset : Nat) : List Val → List Val
  | []      => []
  | v :: vs => shift_val cutoff offset v :: shift_listVal cutoff offset vs

/-- Shift a heap by inserting `padding` at position `cutoff`. All cell
    values get their internal indices shifted (cells with `AllBelow
    cutoff` are unaffected by this — `shift_val` is identity on them —
    so in practice this is exactly "insert `padding` at `cutoff`").
    Defining it uniformly via `h.map shift_val` makes the commutativity
    lemma `(shift_heap)[shift_idx i]? = (h[i]?).map shift_val` clean. -/
def shift_heap (cutoff : Nat) (padding : Heap) (h : Heap) : Heap :=
  (h.map (shift_val cutoff padding.length)).take cutoff ++ padding ++
    (h.map (shift_val cutoff padding.length)).drop cutoff

def shift_state (cutoff : Nat) (padding : Heap) (s : RunState) : RunState :=
  { heap := shift_heap cutoff padding s.heap, policy := s.policy }

/-! ## Injectivity of shift -/

theorem shift_idx_injective (cutoff offset : Nat) :
    ∀ i j, shift_idx cutoff offset i = shift_idx cutoff offset j → i = j := by
  intro i j h
  unfold shift_idx at h
  by_cases hi : i < cutoff
  · by_cases hj : j < cutoff
    · rw [if_pos hi, if_pos hj] at h; exact h
    · rw [if_pos hi, if_neg hj] at h; omega
  · by_cases hj : j < cutoff
    · rw [if_neg hi, if_pos hj] at h; omega
    · rw [if_neg hi, if_neg hj] at h; omega

mutual
  theorem shift_val_injective (cutoff offset : Nat) :
      ∀ a b : Val, shift_val cutoff offset a = shift_val cutoff offset b → a = b
    | .num _,   .num _,   h => by simp [shift_val] at h; exact h ▸ rfl
    | .num _,   .bool _,  h => by simp [shift_val] at h
    | .num _,   .nilV,    h => by simp [shift_val] at h
    | .num _,   .sym _,   h => by simp [shift_val] at h
    | .num _,   .cons _ _, h => by simp [shift_val] at h
    | .num _,   .prim _,  h => by simp [shift_val] at h
    | .num _,   .builtinBaseApply, h => by simp [shift_val] at h
    | .num _,   .closure _ _ _, h => by simp [shift_val] at h
    | .bool _,  .num _,   h => by simp [shift_val] at h
    | .bool _,  .bool _,  h => by simp [shift_val] at h; exact h ▸ rfl
    | .bool _,  .nilV,    h => by simp [shift_val] at h
    | .bool _,  .sym _,   h => by simp [shift_val] at h
    | .bool _,  .cons _ _, h => by simp [shift_val] at h
    | .bool _,  .prim _,  h => by simp [shift_val] at h
    | .bool _,  .builtinBaseApply, h => by simp [shift_val] at h
    | .bool _,  .closure _ _ _, h => by simp [shift_val] at h
    | .nilV,    .num _,   h => by simp [shift_val] at h
    | .nilV,    .bool _,  h => by simp [shift_val] at h
    | .nilV,    .nilV,    _ => rfl
    | .nilV,    .sym _,   h => by simp [shift_val] at h
    | .nilV,    .cons _ _, h => by simp [shift_val] at h
    | .nilV,    .prim _,  h => by simp [shift_val] at h
    | .nilV,    .builtinBaseApply, h => by simp [shift_val] at h
    | .nilV,    .closure _ _ _, h => by simp [shift_val] at h
    | .sym _,   .num _,   h => by simp [shift_val] at h
    | .sym _,   .bool _,  h => by simp [shift_val] at h
    | .sym _,   .nilV,    h => by simp [shift_val] at h
    | .sym _,   .sym _,   h => by simp [shift_val] at h; exact h ▸ rfl
    | .sym _,   .cons _ _, h => by simp [shift_val] at h
    | .sym _,   .prim _,  h => by simp [shift_val] at h
    | .sym _,   .builtinBaseApply, h => by simp [shift_val] at h
    | .sym _,   .closure _ _ _, h => by simp [shift_val] at h
    | .cons _ _, .num _,   h => by simp [shift_val] at h
    | .cons _ _, .bool _,  h => by simp [shift_val] at h
    | .cons _ _, .nilV,    h => by simp [shift_val] at h
    | .cons _ _, .sym _,   h => by simp [shift_val] at h
    | .cons xa ya, .cons xb yb, h => by
        simp [shift_val] at h
        obtain ⟨hx, hy⟩ := h
        rw [shift_val_injective cutoff offset xa xb hx,
            shift_val_injective cutoff offset ya yb hy]
    | .cons _ _, .prim _,  h => by simp [shift_val] at h
    | .cons _ _, .builtinBaseApply, h => by simp [shift_val] at h
    | .cons _ _, .closure _ _ _, h => by simp [shift_val] at h
    | .prim _,  .num _,   h => by simp [shift_val] at h
    | .prim _,  .bool _,  h => by simp [shift_val] at h
    | .prim _,  .nilV,    h => by simp [shift_val] at h
    | .prim _,  .sym _,   h => by simp [shift_val] at h
    | .prim _,  .cons _ _, h => by simp [shift_val] at h
    | .prim _,  .prim _,  h => by simp [shift_val] at h; exact h ▸ rfl
    | .prim _,  .builtinBaseApply, h => by simp [shift_val] at h
    | .prim _,  .closure _ _ _, h => by simp [shift_val] at h
    | .builtinBaseApply, .num _,   h => by simp [shift_val] at h
    | .builtinBaseApply, .bool _,  h => by simp [shift_val] at h
    | .builtinBaseApply, .nilV,    h => by simp [shift_val] at h
    | .builtinBaseApply, .sym _,   h => by simp [shift_val] at h
    | .builtinBaseApply, .cons _ _, h => by simp [shift_val] at h
    | .builtinBaseApply, .prim _,  h => by simp [shift_val] at h
    | .builtinBaseApply, .builtinBaseApply, _ => rfl
    | .builtinBaseApply, .closure _ _ _, h => by simp [shift_val] at h
    | .closure _ _ _, .num _,   h => by simp [shift_val] at h
    | .closure _ _ _, .bool _,  h => by simp [shift_val] at h
    | .closure _ _ _, .nilV,    h => by simp [shift_val] at h
    | .closure _ _ _, .sym _,   h => by simp [shift_val] at h
    | .closure _ _ _, .cons _ _, h => by simp [shift_val] at h
    | .closure _ _ _, .prim _,  h => by simp [shift_val] at h
    | .closure _ _ _, .builtinBaseApply, h => by simp [shift_val] at h
    | .closure psa bdya cenva, .closure psb bdyb cenvb, h => by
        simp [shift_val] at h
        obtain ⟨hps, hbdy, hcenv⟩ := h
        rw [hps, hbdy, shift_env_injective cutoff offset cenva cenvb hcenv]

  theorem shift_env_injective (cutoff offset : Nat) :
      ∀ a b : Env, shift_env cutoff offset a = shift_env cutoff offset b → a = b
    | .nil, .nil, _ => rfl
    | .nil, .cons _ _ _, h => by simp [shift_env] at h
    | .cons _ _ _, .nil, h => by simp [shift_env] at h
    | .cons name_a idx_a rest_a, .cons name_b idx_b rest_b, h => by
        simp [shift_env] at h
        obtain ⟨hname, hidx, hrest⟩ := h
        rw [hname, shift_idx_injective cutoff offset idx_a idx_b hidx,
            shift_env_injective cutoff offset rest_a rest_b hrest]
end

/-! ## Structural facts about shift -/

theorem shift_idx_below {cutoff offset i : Nat} (h : i < cutoff) :
    shift_idx cutoff offset i = i := by
  unfold shift_idx; rw [if_pos h]

theorem shift_idx_above {cutoff offset i : Nat} (h : ¬ i < cutoff) :
    shift_idx cutoff offset i = i + offset := by
  unfold shift_idx; rw [if_neg h]

theorem shift_listVal_length (cutoff offset : Nat) (xs : List Val) :
    (shift_listVal cutoff offset xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [shift_listVal, ih]

theorem shift_listVal_append (cutoff offset : Nat) (xs ys : List Val) :
    shift_listVal cutoff offset (xs ++ ys) =
      shift_listVal cutoff offset xs ++ shift_listVal cutoff offset ys := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [shift_listVal, ih]

theorem shift_heap_length (cutoff : Nat) (padding h : Heap) :
    (shift_heap cutoff padding h).length = h.length + padding.length := by
  unfold shift_heap
  simp only [List.length_append, List.length_take, List.length_drop, List.length_map]
  omega

/-- Structural "all bindings below cutoff" predicate on `Env`. Stronger
    than `EnvValid` (which only constrains lookups, not shadowed
    bindings), but holds for any `Env` constructed by the runner — every
    binding is added at the current `heap.length`, which only grows. -/
def Env.AllBelow (cutoff : Nat) : Env → Prop
  | .nil               => True
  | .cons _ idx rest   => idx < cutoff ∧ Env.AllBelow cutoff rest

/-- Structural counterpart on values: closures' captured envs are
    `AllBelow`. Other constructors are heap-independent. -/
def Val.AllBelow (cutoff : Nat) : Val → Prop
  | .num _              => True
  | .bool _             => True
  | .nilV               => True
  | .sym _              => True
  | .prim _             => True
  | .builtinBaseApply   => True
  | .cons x y           => Val.AllBelow cutoff x ∧ Val.AllBelow cutoff y
  | .closure _ _ cenv   => Env.AllBelow cutoff cenv

def ListVal.AllBelow (cutoff : Nat) : List Val → Prop
  | []      => True
  | v :: vs => Val.AllBelow cutoff v ∧ ListVal.AllBelow cutoff vs

theorem Env.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {env : Env}, Env.AllBelow cutoff env → Env.AllBelow cutoff' env
  | .nil,           _   => trivial
  | .cons _ _ rest, ⟨h_idx, h_rest⟩ =>
      ⟨Nat.lt_of_lt_of_le h_idx h_le, Env.AllBelow.mono h_le h_rest⟩

theorem Val.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {v : Val}, Val.AllBelow cutoff v → Val.AllBelow cutoff' v
  | .num _,            _ => trivial
  | .bool _,           _ => trivial
  | .nilV,             _ => trivial
  | .sym _,            _ => trivial
  | .prim _,           _ => trivial
  | .builtinBaseApply, _ => trivial
  | .cons x y,         ⟨hx, hy⟩ => ⟨Val.AllBelow.mono h_le hx, Val.AllBelow.mono h_le hy⟩
  | .closure _ _ _,    h => Env.AllBelow.mono h_le h

theorem ListVal.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {xs : List Val}, ListVal.AllBelow cutoff xs → ListVal.AllBelow cutoff' xs
  | [],      _ => trivial
  | _ :: _, ⟨h, t⟩ => ⟨Val.AllBelow.mono h_le h, ListVal.AllBelow.mono h_le t⟩

/-! ## Deep validity (carries `Env.AllBelow`/`Val.AllBelow` strength)

    `EnvValid` / `ValValid` are *shallow* (only check looked-up cells in
    envs). `EnvDeep` / `ValDeep` walk the structure and check every cell
    — exactly what's needed to derive `Env.AllBelow heap.length env` /
    `Val.AllBelow heap.length v`. Runtime envs / heap-stored values
    satisfy these because they're built incrementally with each binding
    pointing to a freshly-allocated cell. -/

def EnvDeep : Env → Heap → Prop
  | .nil,             _ => True
  | .cons _ idx rest, h => idx < h.length ∧ EnvDeep rest h

def ValDeep : Val → Heap → Prop
  | .num _,            _ => True
  | .bool _,           _ => True
  | .nilV,             _ => True
  | .sym _,            _ => True
  | .prim _,           _ => True
  | .builtinBaseApply, _ => True
  | .cons x y,         h => ValDeep x h ∧ ValDeep y h
  | .closure _ _ cenv, h => EnvDeep cenv h

def ListValDeep : List Val → Heap → Prop
  | [],      _ => True
  | x :: xs, h => ValDeep x h ∧ ListValDeep xs h

/-- Heap-deep validity: every cell holds a `ValDeep` value. -/
def HeapDeep (h : Heap) : Prop :=
  ∀ (i : Nat) (v : Val), h[i]? = some v → ValDeep v h

theorem EnvDeep.toAllBelow : ∀ {env : Env} {h : Heap},
    EnvDeep env h → Env.AllBelow h.length env
  | Env.nil,           _, _   => trivial
  | Env.cons _ _ rest, _, ⟨h_idx, h_rest⟩ =>
      ⟨h_idx, EnvDeep.toAllBelow h_rest⟩

theorem ValDeep.toAllBelow : ∀ {v : Val} {h : Heap},
    ValDeep v h → Val.AllBelow h.length v
  | .num _,            _, _ => trivial
  | .bool _,           _, _ => trivial
  | .nilV,             _, _ => trivial
  | .sym _,            _, _ => trivial
  | .prim _,           _, _ => trivial
  | .builtinBaseApply, _, _ => trivial
  | .cons x y,         _, ⟨hx, hy⟩ =>
      ⟨ValDeep.toAllBelow hx, ValDeep.toAllBelow hy⟩
  | .closure _ _ _,    _, h => EnvDeep.toAllBelow h

theorem ListValDeep.toAllBelow : ∀ {vs : List Val} {h : Heap},
    ListValDeep vs h → ListVal.AllBelow h.length vs
  | [],      _, _ => trivial
  | _ :: _, _, ⟨hx, hxs⟩ =>
      ⟨ValDeep.toAllBelow hx, ListValDeep.toAllBelow hxs⟩

/-! ## Deep validity is monotone in heap length -/

theorem EnvDeep.length_mono : ∀ {env : Env} {h h' : Heap},
    EnvDeep env h → h.length ≤ h'.length → EnvDeep env h'
  | Env.nil,           _, _, _, _   => trivial
  | Env.cons _ _ rest, _, _, ⟨h_idx, h_rest⟩, h_le =>
      ⟨Nat.lt_of_lt_of_le h_idx h_le, EnvDeep.length_mono h_rest h_le⟩

theorem ValDeep.length_mono : ∀ {v : Val} {h h' : Heap},
    ValDeep v h → h.length ≤ h'.length → ValDeep v h'
  | .num _,            _, _, _,  _   => trivial
  | .bool _,           _, _, _,  _   => trivial
  | .nilV,             _, _, _,  _   => trivial
  | .sym _,            _, _, _,  _   => trivial
  | .prim _,           _, _, _,  _   => trivial
  | .builtinBaseApply, _, _, _,  _   => trivial
  | .cons x y,         _, _, ⟨hx, hy⟩, h_le =>
      ⟨ValDeep.length_mono hx h_le, ValDeep.length_mono hy h_le⟩
  | .closure _ _ _,    _, _, hev, h_le => EnvDeep.length_mono hev h_le

theorem ListValDeep.length_mono : ∀ {vs : List Val} {h h' : Heap},
    ListValDeep vs h → h.length ≤ h'.length → ListValDeep vs h'
  | [],      _, _, _, _ => trivial
  | _ :: _, _, _, ⟨hx, hxs⟩, h_le =>
      ⟨ValDeep.length_mono hx h_le, ListValDeep.length_mono hxs h_le⟩

/-! ## Deep validity of the initial runtime state

    The runtime starts with a heap of atoms only (`.prim`,
    `.builtinBaseApply`), so `HeapDeep` is trivially established.
    Each `Env.cons` in `buildBindings` uses the previous heap length
    as its index, which is `< new heap length` after `alloc`. -/

/-- Atoms (non-closure, non-cons values) are `ValDeep` in any heap:
    they have no embedded indices to bound. -/
theorem ValDeep.atom : ∀ {v : Val} {h : Heap},
    (∀ ps body cenv, v ≠ .closure ps body cenv) →
    (∀ x y, v ≠ .cons x y) → ValDeep v h
  | .num _,            _, _, _ => trivial
  | .bool _,           _, _, _ => trivial
  | .nilV,             _, _, _ => trivial
  | .sym _,            _, _, _ => trivial
  | .prim _,           _, _, _ => trivial
  | .builtinBaseApply, _, _, _ => trivial
  | .cons x y,         _, _, h_no_cons => absurd rfl (h_no_cons x y)
  | .closure ps body cenv, _, h_no_closure, _ => absurd rfl (h_no_closure ps body cenv)

/-- Append-alloc preserves `HeapDeep` when the appended value is
    `ValDeep` in the new heap. -/
theorem HeapDeep.alloc_atom {h : Heap} (h_deep : HeapDeep h) (v : Val)
    (hv_atom : ∀ ps body cenv, v ≠ .closure ps body cenv)
    (hv_no_cons : ∀ x y, v ≠ .cons x y) :
    HeapDeep (h ++ [v]) := by
  intro i v' hi
  by_cases h_lt : i < h.length
  · have h_eq : (h ++ [v])[i]? = h[i]? := getElem?_prefix h [v] i h_lt
    rw [h_eq] at hi
    exact ValDeep.length_mono (h_deep i v' hi) (by simp [List.length_append])
  · have h_le : h.length ≤ i := Nat.le_of_not_lt h_lt
    have h_eq : (h ++ [v])[i]? = [v][i - h.length]? :=
      List.getElem?_append_right h_le
    rw [h_eq] at hi
    -- [v][k]? = some _ iff k = 0 (since [v] has length 1).
    cases h_off : i - h.length with
    | zero =>
        rw [h_off] at hi
        simp at hi
        subst hi
        exact ValDeep.atom hv_atom hv_no_cons
    | succ k =>
        rw [h_off] at hi
        simp at hi

/-- `buildBindings` over atom-valued pairs: produces an `EnvDeep` env
    in a `HeapDeep` heap. -/
theorem buildBindings_atom_deep :
    ∀ (acc_env : Env) (acc_heap : Heap) (pairs : List (String × Val)),
      EnvDeep acc_env acc_heap → HeapDeep acc_heap →
      (∀ p ∈ pairs, (∀ ps body cenv, p.2 ≠ .closure ps body cenv) ∧
                    (∀ x y, p.2 ≠ .cons x y)) →
      let result := pairs.foldl
        (fun (acc : Env × Heap) (kv : String × Val) =>
          let (env, h) := acc
          let (h', idx) := h.alloc kv.2
          (.cons kv.1 idx env, h'))
        (acc_env, acc_heap)
      EnvDeep result.1 result.2 ∧ HeapDeep result.2
  | _, _, [], h_env, h_heap, _ => ⟨h_env, h_heap⟩
  | acc_env, acc_heap, (key, val) :: rest, h_env, h_heap, h_atoms => by
      simp only [List.foldl, Heap.alloc]
      have h_v_atom : (∀ ps body cenv, val ≠ .closure ps body cenv) ∧
                      (∀ x y, val ≠ .cons x y) :=
        h_atoms (key, val) (List.mem_cons_self)
      have h_heap' : HeapDeep (acc_heap ++ [val]) :=
        HeapDeep.alloc_atom h_heap val h_v_atom.1 h_v_atom.2
      have h_env' : EnvDeep (.cons key acc_heap.length acc_env) (acc_heap ++ [val]) := by
        refine ⟨?_, ?_⟩
        · simp [List.length_append]
        · exact EnvDeep.length_mono h_env (by simp [List.length_append])
      have h_atoms_rest : ∀ p ∈ rest,
          (∀ ps body cenv, p.2 ≠ .closure ps body cenv) ∧
          (∀ x y, p.2 ≠ .cons x y) :=
        fun p hp => h_atoms p (List.mem_cons.mpr (Or.inr hp))
      exact buildBindings_atom_deep _ _ rest h_env' h_heap' h_atoms_rest

/-- The initial base environment is Deep-valid: heap holds only
    `.prim` atoms, env binds them at consecutive heap indices. -/
theorem initBaseEnv_deep :
    EnvDeep initBaseEnv.1 initBaseEnv.2 ∧ HeapDeep initBaseEnv.2 := by
  unfold initBaseEnv
  have h_nil_heap : HeapDeep ([] : Heap) := fun i v hi => by simp at hi
  apply buildBindings_atom_deep .nil [] _ trivial h_nil_heap
  intro p hp
  -- Each pair p has p.2 = .prim _; show p.2 is neither a closure nor a cons.
  -- We prove ∃ s, p.2 = .prim s via case analysis on `hp : p ∈ list`.
  have h_prim : ∃ s, p.2 = .prim s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;>
      (rw [hp]; exact ⟨_, rfl⟩)
  obtain ⟨s, h_p2⟩ := h_prim
  exact ⟨fun _ _ _ h => by rw [h_p2] at h; injection h,
         fun _ _ h => by rw [h_p2] at h; injection h⟩

/-- The initial state's heap is `HeapDeep`, the user env and meta env
    are `EnvDeep`. The runtime invariant the runner needs to bootstrap
    `applyDirect_heap_extend_weak`'s Deep-validity preconditions. -/
theorem initState_deep (defaultPolicy : BlackPolicy) :
    EnvDeep (initState defaultPolicy).1 (initState defaultPolicy).2.2.heap ∧
    EnvDeep (initState defaultPolicy).2.1 (initState defaultPolicy).2.2.heap ∧
    HeapDeep (initState defaultPolicy).2.2.heap := by
  unfold initState
  obtain ⟨h_env, h_heap⟩ := initBaseEnv_deep
  -- After alloc of .builtinBaseApply, heap = initBaseEnv.2 ++ [.builtinBaseApply].
  have h_alloc_heap : HeapDeep (initBaseEnv.2 ++ [.builtinBaseApply]) :=
    HeapDeep.alloc_atom h_heap .builtinBaseApply
      (by intro _ _ _ h; simp at h) (by intro _ _ h; simp at h)
  have h_user_alloc : EnvDeep initBaseEnv.1 (initBaseEnv.2 ++ [.builtinBaseApply]) :=
    EnvDeep.length_mono h_env (by simp [List.length_append])
  have h_meta_alloc :
      EnvDeep (.cons "base-apply" initBaseEnv.2.length initBaseEnv.1)
              (initBaseEnv.2 ++ [.builtinBaseApply]) := by
    refine ⟨?_, ?_⟩
    · simp [List.length_append]
    · exact h_user_alloc
  refine ⟨?_, ?_, ?_⟩
  · simp only [Heap.alloc]; exact h_user_alloc
  · simp only [Heap.alloc]; exact h_meta_alloc
  · simp only [Heap.alloc]; exact h_alloc_heap

/-- Closed values are vacuously `AllBelow` at any cutoff: no closures
    means no embedded indices. -/
theorem closedValB_AllBelow (cutoff : Nat) :
    ∀ (v : Val), closedValB v = true → Val.AllBelow cutoff v
  | .num _,            _ => trivial
  | .bool _,           _ => trivial
  | .nilV,             _ => trivial
  | .sym _,            _ => trivial
  | .prim _,           _ => trivial
  | .builtinBaseApply, _ => trivial
  | .cons x y, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_AllBelow cutoff x hc.1, closedValB_AllBelow cutoff y hc.2⟩
  | .closure _ _ _, hc => by simp [closedValB] at hc

/-- If all of `env`'s bindings are below `cutoff`, shifting is a no-op. -/
theorem shift_env_id (cutoff offset : Nat) :
    ∀ {env : Env}, Env.AllBelow cutoff env →
      shift_env cutoff offset env = env
  | .nil,            _ => rfl
  | .cons name idx rest, ⟨h_idx, h_rest⟩ => by
      simp only [shift_env, shift_idx_below h_idx, shift_env_id cutoff offset h_rest]

theorem shift_val_id (cutoff offset : Nat) :
    ∀ {v : Val}, Val.AllBelow cutoff v → shift_val cutoff offset v = v
  | .num _,            _ => rfl
  | .bool _,           _ => rfl
  | .nilV,             _ => rfl
  | .sym _,            _ => rfl
  | .prim _,           _ => rfl
  | .builtinBaseApply, _ => rfl
  | .cons x y,         ⟨hx, hy⟩ => by
      simp only [shift_val, shift_val_id cutoff offset hx, shift_val_id cutoff offset hy]
  | .closure ps body cenv, h => by
      simp only [shift_val, shift_env_id cutoff offset h]

theorem shift_listVal_id (cutoff offset : Nat) :
    ∀ {xs : List Val}, ListVal.AllBelow cutoff xs →
      shift_listVal cutoff offset xs = xs
  | [],      _ => rfl
  | _ :: _, ⟨h, t⟩ => by
      simp only [shift_listVal, shift_val_id cutoff offset h,
                 shift_listVal_id cutoff offset t]

/-! ## `shift` commutes with key operations -/

/-- `Env.lookup` commutes with shift: shifted env's lookup returns the
    shifted index. -/
theorem shift_env_lookup (cutoff offset : Nat) :
    ∀ (env : Env) (x : String) (i : Nat),
      env.lookup x = some i →
      (shift_env cutoff offset env).lookup x = some (shift_idx cutoff offset i)
  | .nil, _, _, h => by simp [Env.lookup] at h
  | .cons name idx rest, x, i, h => by
      simp only [Env.lookup] at h
      simp only [shift_env, Env.lookup]
      by_cases h_eq : name == x
      · simp only [h_eq, if_true] at h ⊢
        injection h with h_idx
        subst h_idx
        rfl
      · simp only [h_eq, if_false] at h ⊢
        exact shift_env_lookup cutoff offset rest x i h

/-- `Env.lookup` commutes with shift on `none` results too. -/
theorem shift_env_lookup_none (cutoff offset : Nat) :
    ∀ (env : Env) (x : String),
      env.lookup x = none →
      (shift_env cutoff offset env).lookup x = none
  | .nil, _, _ => rfl
  | .cons name idx rest, x, h => by
      simp only [Env.lookup] at h
      simp only [shift_env, Env.lookup]
      by_cases h_eq : name == x
      · simp only [h_eq, if_true] at h
        exact absurd h (by simp)
      · simp only [h_eq, if_false] at h ⊢
        exact shift_env_lookup_none cutoff offset rest x h

/-! ## Heap operations commute with shift -/

theorem shift_heap_getElem? (cutoff : Nat) (padding h : Heap) (i : Nat)
    (h_cutoff : cutoff ≤ h.length) :
    (shift_heap cutoff padding h)[shift_idx cutoff padding.length i]?
      = (h[i]?).map (shift_val cutoff padding.length) := by
  unfold shift_heap shift_idx
  have sh_len : (h.map (shift_val cutoff padding.length)).length = h.length := by
    simp [List.length_map]
  have sh_get : ∀ (k : Nat), (h.map (shift_val cutoff padding.length))[k]?
                  = (h[k]?).map (shift_val cutoff padding.length) := by
    intro k; simp [List.getElem?_map]
  have h_take_len : ((h.map (shift_val cutoff padding.length)).take cutoff).length = cutoff := by
    rw [List.length_take, sh_len]; omega
  have h_drop_len :
      ((h.map (shift_val cutoff padding.length)).drop cutoff).length = h.length - cutoff := by
    rw [List.length_drop, sh_len]
  by_cases h_lt : i < cutoff
  · rw [if_pos h_lt]
    have h_take_lt :
        i < ((h.map (shift_val cutoff padding.length)).take cutoff).length := by
      rw [h_take_len]; exact h_lt
    have h_left_lt :
        i < ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length := by
      rw [List.length_append, h_take_len]; omega
    rw [List.getElem?_append_left h_left_lt]
    rw [List.getElem?_append_left h_take_lt]
    rw [List.getElem?_take]
    rw [if_pos h_lt]
    exact sh_get i
  · rw [if_neg h_lt]
    have h_le : cutoff ≤ i := Nat.le_of_not_lt h_lt
    have h_left_len :
        ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length
          = cutoff + padding.length := by
      rw [List.length_append, h_take_len]
    have h_skip_left :
        ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length
          ≤ i + padding.length := by rw [h_left_len]; omega
    rw [List.getElem?_append_right h_skip_left]
    have h_idx_eq :
        i + padding.length
          - ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length
          = i - cutoff := by rw [h_left_len]; omega
    rw [h_idx_eq]
    rw [List.getElem?_drop]
    have h_eq : cutoff + (i - cutoff) = i := by omega
    rw [h_eq]
    exact sh_get i

/-- `(shift_heap)`-shape lookup at `shift_idx idx` always lands within
    bounds when `idx < h.length` and `cutoff ≤ h.length`. -/
theorem shift_idx_lt_shift_heap_length (cutoff : Nat) (padding h : Heap) (idx : Nat)
    (h_cutoff : cutoff ≤ h.length) (h_idx_lt : idx < h.length) :
    shift_idx cutoff padding.length idx < (shift_heap cutoff padding h).length := by
  rw [shift_heap_length]
  unfold shift_idx
  by_cases h_lt : idx < cutoff
  · rw [if_pos h_lt]; omega
  · rw [if_neg h_lt]; omega

/-- A position `k` in the *padding region* (`cutoff ≤ k < cutoff + padding.length`)
    of `shift_heap` is just the corresponding `padding[k - cutoff]?`. -/
theorem shift_heap_getElem?_padding (cutoff : Nat) (padding h : Heap) (k : Nat)
    (h_cutoff : cutoff ≤ h.length)
    (h_lo : cutoff ≤ k) (h_hi : k < cutoff + padding.length) :
    (shift_heap cutoff padding h)[k]? = padding[k - cutoff]? := by
  unfold shift_heap
  have h_take_len : ((h.map (shift_val cutoff padding.length)).take cutoff).length = cutoff := by
    rw [List.length_take, List.length_map]; omega
  have h_left_len :
      ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length
        = cutoff + padding.length := by
    rw [List.length_append, h_take_len]
  have h_skip : ((h.map (shift_val cutoff padding.length)).take cutoff).length ≤ k := by
    rw [h_take_len]; exact h_lo
  have h_left_lt : k < ((h.map (shift_val cutoff padding.length)).take cutoff ++ padding).length := by
    rw [h_left_len]; exact h_hi
  rw [List.getElem?_append_left h_left_lt]
  rw [List.getElem?_append_right h_skip]
  rw [h_take_len]

/-- `shift_heap` length when used with `Heap.update` (length preserved). -/
theorem shift_heap_update_length' (cutoff : Nat) (padding h : Heap) (idx : Nat) (v : Val)
    (h_cutoff : cutoff ≤ h.length) :
    (shift_heap cutoff padding (h.update idx v)).length
      = (shift_heap cutoff padding h).length := by
  rw [shift_heap_length, shift_heap_length, Heap.update_length]

/-- `shift_listVal` is just `List.map shift_val`. -/
theorem shift_listVal_eq_map (cutoff offset : Nat) :
    ∀ (xs : List Val),
      shift_listVal cutoff offset xs = xs.map (shift_val cutoff offset)
  | []      => rfl
  | _ :: xs => by simp [shift_listVal, shift_listVal_eq_map cutoff offset xs]

/-- `listToVal` commutes with shift. -/
theorem shift_val_listToVal (cutoff offset : Nat) :
    ∀ (xs : List Val),
      shift_val cutoff offset (listToVal xs) =
        listToVal (shift_listVal cutoff offset xs)
  | []      => rfl
  | _ :: xs => by simp [listToVal, shift_listVal, shift_val, shift_val_listToVal cutoff offset xs]

/-- `valToList` commutes with shift. -/
theorem shift_listVal_valToList (cutoff offset : Nat) :
    ∀ (v : Val),
      valToList (shift_val cutoff offset v) =
        (valToList v).map (shift_listVal cutoff offset)
  | .nilV               => rfl
  | .cons x xs => by
      simp only [shift_val, valToList]
      rw [shift_listVal_valToList cutoff offset xs]
      cases valToList xs with
      | none => rfl
      | some rest => simp [shift_listVal]
  | .num _              => rfl
  | .bool _             => rfl
  | .sym _              => rfl
  | .prim _             => rfl
  | .builtinBaseApply   => rfl
  | .closure _ _ _      => rfl

/-- Heap append commutes with shift, when `cutoff ≤ h.length`. -/
theorem shift_heap_append (cutoff : Nat) (padding h ext : Heap)
    (h_cutoff : cutoff ≤ h.length) :
    shift_heap cutoff padding (h ++ ext) =
      shift_heap cutoff padding h ++ ext.map (shift_val cutoff padding.length) := by
  unfold shift_heap
  simp only [List.map_append]
  rw [List.take_append_of_le_length (by rw [List.length_map]; exact h_cutoff)]
  rw [List.drop_append_of_le_length (by rw [List.length_map]; exact h_cutoff)]
  -- Goal: take_h ++ padding ++ (drop_h ++ map_ext) = (take_h ++ padding ++ drop_h) ++ map_ext.
  simp [List.append_assoc]

/-- Heap update commutes with shift: shifting an updated heap equals
    updating the shifted heap at the shifted index. -/
theorem shift_heap_update (cutoff : Nat) (padding h : Heap) (idx : Nat) (v : Val)
    (h_cutoff : cutoff ≤ h.length) (h_idx_lt : idx < h.length) :
    shift_heap cutoff padding (h.update idx v) =
      (shift_heap cutoff padding h).update
        (shift_idx cutoff padding.length idx)
        (shift_val cutoff padding.length v) := by
  apply List.ext_getElem?
  intro k
  have h_cutoff' : cutoff ≤ (h.update idx v).length := by
    rw [Heap.update_length]; exact h_cutoff
  by_cases h_eq : k = shift_idx cutoff padding.length idx
  · -- Updated position: both sides give some (shift_val v).
    subst h_eq
    rw [shift_heap_getElem? cutoff padding (h.update idx v) idx h_cutoff']
    rw [Heap.update_get_eq h idx v h_idx_lt]
    have h_shifted_lt :
        shift_idx cutoff padding.length idx < (shift_heap cutoff padding h).length :=
      shift_idx_lt_shift_heap_length cutoff padding h idx h_cutoff h_idx_lt
    rw [Heap.update_get_eq (shift_heap cutoff padding h)
          (shift_idx cutoff padding.length idx)
          (shift_val cutoff padding.length v) h_shifted_lt]
    rfl
  · -- Non-updated position k ≠ shift_idx idx.
    rw [Heap.update_get_neq _ _ _ _ h_eq]
    -- Three regions for k: < cutoff (use shift_heap_getElem? at original-idx k),
    -- in padding [cutoff, cutoff+padding.length) (use shift_heap_getElem?_padding),
    -- ≥ cutoff + padding.length (use shift_heap_getElem? at original-idx k - padding.length).
    by_cases h_k_below : k < cutoff
    · -- Region 1: k < cutoff. shift_idx k = k.
      have h_shift_k : shift_idx cutoff padding.length k = k := shift_idx_below h_k_below
      rw [show k = shift_idx cutoff padding.length k from h_shift_k.symm,
          shift_heap_getElem? cutoff padding (h.update idx v) k h_cutoff',
          shift_heap_getElem? cutoff padding h k h_cutoff]
      have h_k_ne_idx : k ≠ idx := by
        intro h_eq_idx
        apply h_eq
        have h_idx_below : idx < cutoff := by rw [← h_eq_idx]; exact h_k_below
        rw [h_eq_idx, shift_idx_below h_idx_below]
      rw [Heap.update_get_neq _ _ _ _ h_k_ne_idx]
    · -- Region 2 or 3.
      have h_k_ge : cutoff ≤ k := Nat.le_of_not_lt h_k_below
      by_cases h_k_pad : k < cutoff + padding.length
      · -- Region 2: padding region. Both sides give padding[k - cutoff]?.
        rw [shift_heap_getElem?_padding cutoff padding (h.update idx v) k h_cutoff' h_k_ge h_k_pad]
        rw [shift_heap_getElem?_padding cutoff padding h k h_cutoff h_k_ge h_k_pad]
      · -- Region 3: k ≥ cutoff + padding.length.
        have h_k_high : cutoff + padding.length ≤ k := Nat.le_of_not_lt h_k_pad
        -- shift_idx (k - padding.length) = k. Use shift_heap_getElem? at orig idx k - padding.length.
        have h_orig_ge : cutoff ≤ k - padding.length := by omega
        have h_shifted_eq : shift_idx cutoff padding.length (k - padding.length) = k := by
          unfold shift_idx
          rw [if_neg (by omega : ¬ k - padding.length < cutoff)]
          omega
        rw [← h_shifted_eq]
        rw [shift_heap_getElem? cutoff padding (h.update idx v) (k - padding.length) h_cutoff']
        rw [shift_heap_getElem? cutoff padding h (k - padding.length) h_cutoff]
        have h_orig_ne_idx : k - padding.length ≠ idx := by
          intro h_eq_idx
          apply h_eq
          rw [← h_shifted_eq, h_eq_idx]
        rw [Heap.update_get_neq _ _ _ _ h_orig_ne_idx]

/-- General `shift_heap_update`: works regardless of bounds. If `idx`
    is out of bounds on side A, both updates are no-ops. -/
theorem shift_heap_update_general (cutoff : Nat) (padding h : Heap) (idx : Nat) (v : Val)
    (h_cutoff : cutoff ≤ h.length) :
    shift_heap cutoff padding (h.update idx v) =
      (shift_heap cutoff padding h).update
        (shift_idx cutoff padding.length idx)
        (shift_val cutoff padding.length v) := by
  by_cases h_lt : idx < h.length
  · exact shift_heap_update cutoff padding h idx v h_cutoff h_lt
  · -- Out-of-bounds: both updates are no-ops.
    have h_oob_a : h.length ≤ idx := Nat.le_of_not_lt h_lt
    rw [Heap.update_oob h idx v h_oob_a]
    -- Side B: shift_idx idx ≥ cutoff (since idx ≥ cutoff because idx ≥ h.length ≥ cutoff).
    have h_idx_ge_cutoff : cutoff ≤ idx := Nat.le_trans h_cutoff h_oob_a
    have h_shift_idx : shift_idx cutoff padding.length idx = idx + padding.length := by
      unfold shift_idx
      rw [if_neg (by omega : ¬ idx < cutoff)]
    have h_shift_idx_oob :
        (shift_heap cutoff padding h).length
          ≤ shift_idx cutoff padding.length idx := by
      rw [shift_heap_length, h_shift_idx]; omega
    rw [Heap.update_oob _ _ _ h_shift_idx_oob]

/-- Helper: `List.map (shift_val cutoff offset)` is identity on a list
    where every element is `Val.AllBelow cutoff`. -/
private theorem map_shift_val_eq_self_of_AllBelow (cutoff offset : Nat) :
    ∀ (l : List Val), (∀ v ∈ l, Val.AllBelow cutoff v) →
    l.map (shift_val cutoff offset) = l
  | [], _ => rfl
  | x :: xs, hp => by
      simp only [List.map_cons]
      have hx : Val.AllBelow cutoff x := hp x List.mem_cons_self
      have hxs : ∀ v ∈ xs, Val.AllBelow cutoff v :=
        fun v hv => hp v (List.mem_cons.mpr (Or.inr hv))
      rw [shift_val_id cutoff offset hx,
          map_shift_val_eq_self_of_AllBelow cutoff offset xs hxs]

/-- When the heap is `HeapDeep` and `cutoff = h.length`, shifting just
    appends the padding: every value in `h` is `AllBelow h.length`,
    so `shift_val` is identity on it. -/
theorem shift_heap_id_of_deep (padding : Heap) :
    ∀ (h : Heap), HeapDeep h →
    shift_heap h.length padding h = h ++ padding := by
  intro h h_deep
  unfold shift_heap
  -- Each element of h is Val.AllBelow h.length, so map of shift_val is identity.
  have h_all_below : ∀ v ∈ h, Val.AllBelow h.length v := by
    intro v hv_mem
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hv_mem
    exact ValDeep.toAllBelow (h_deep i v hi)
  rw [map_shift_val_eq_self_of_AllBelow h.length padding.length h h_all_below]
  rw [List.take_length, List.drop_length]
  simp

/-! ## Self-shift weak bisim: a value/env is weakly-bisim-related to
    its own shift in the (heap, shifted-heap) pair.

    Mutual induction on depth + structural induction on value / env. -/

/-- Joint statement: at every depth n, every `ValValid v h` is
    `ValVis_aux_weak n` related to `shift_val v`, and every `EnvValid
    env h` is `EnvVis_aux_weak n` related to `shift_env env`. -/
private theorem valVis_self_shift_aux (cutoff : Nat) (padding : Heap) :
    ∀ (n : Nat) (h : Heap), HeapValid h → cutoff ≤ h.length →
    (∀ (v : Val), ValValid v h →
      ValVis_aux_weak n v (shift_val cutoff padding.length v)
        h (shift_heap cutoff padding h)) ∧
    (∀ (env : Env), EnvValid env h →
      EnvVis_aux_weak n env (shift_env cutoff padding.length env)
        h (shift_heap cutoff padding h)) := by
  intro n
  induction n with
  | zero =>
      intro h h_heap_valid h_cutoff
      refine ⟨?_, ?_⟩
      · intro _ _; trivial
      · intro env hev x
        cases hxe : env.lookup x with
        | none => simp [shift_env_lookup_none cutoff padding.length env x hxe]
        | some idx =>
            rw [shift_env_lookup cutoff padding.length env x idx hxe]
            simp only
            have h_idx_lt : idx < h.length := hev x idx hxe
            cases hv : h[idx]? with
            | none =>
                exfalso
                rw [List.getElem?_eq_none_iff] at hv
                omega
            | some v =>
                rw [shift_heap_getElem? cutoff padding h idx h_cutoff, hv]
                simp only [Option.map_some]
                trivial
  | succ k ih =>
      intro h h_heap_valid h_cutoff
      have ih_h := ih h h_heap_valid h_cutoff
      obtain ⟨ih_val_k, ih_env_k⟩ := ih_h
      refine ⟨?_, ?_⟩
      · -- value case at depth k+1
        intro v hv
        cases v with
        | num a => simp [shift_val, ValVis_aux_weak]
        | bool a => simp [shift_val, ValVis_aux_weak]
        | nilV => simp [shift_val, ValVis_aux_weak]
        | sym a => simp [shift_val, ValVis_aux_weak]
        | prim a => simp [shift_val, ValVis_aux_weak]
        | builtinBaseApply => simp [shift_val, ValVis_aux_weak]
        | cons x y =>
            obtain ⟨hx, hy⟩ := hv
            simp only [shift_val, ValVis_aux_weak]
            exact ⟨ih_val_k x hx, ih_val_k y hy⟩
        | closure ps body cenv =>
            have hev : EnvValid cenv h := hv
            simp only [shift_val]
            rw [ValVis_aux_weak_closure]
            exact ⟨rfl, rfl, ih_env_k cenv hev⟩
      · -- env case at depth k+1
        intro env hev x
        cases hxe : env.lookup x with
        | none => simp [shift_env_lookup_none cutoff padding.length env x hxe]
        | some idx =>
            rw [shift_env_lookup cutoff padding.length env x idx hxe]
            simp only
            have h_idx_lt : idx < h.length := hev x idx hxe
            cases hv : h[idx]? with
            | none =>
                exfalso
                rw [List.getElem?_eq_none_iff] at hv
                omega
            | some v =>
                rw [shift_heap_getElem? cutoff padding h idx h_cutoff, hv]
                simp only [Option.map_some]
                have hv_valid : ValValid v h := h_heap_valid idx v hv
                cases v with
                | num a => simp [shift_val, ValVis_aux_weak]
                | bool a => simp [shift_val, ValVis_aux_weak]
                | nilV => simp [shift_val, ValVis_aux_weak]
                | sym a => simp [shift_val, ValVis_aux_weak]
                | prim a => simp [shift_val, ValVis_aux_weak]
                | builtinBaseApply => simp [shift_val, ValVis_aux_weak]
                | cons xx yy =>
                    obtain ⟨hx, hy⟩ := hv_valid
                    simp only [shift_val, ValVis_aux_weak]
                    exact ⟨ih_val_k xx hx, ih_val_k yy hy⟩
                | closure psv bodyv cenvv =>
                    have hev2 : EnvValid cenvv h := hv_valid
                    simp only [shift_val]
                    rw [ValVis_aux_weak_closure]
                    exact ⟨rfl, rfl, ih_env_k cenvv hev2⟩

/-- Surface ValVis_weak self-shift relation. -/
private theorem valVis_weak_self_shift (cutoff : Nat) (padding : Heap)
    (h : Heap) (h_heap : HeapValid h) (h_cutoff : cutoff ≤ h.length)
    (v : Val) (hv : ValValid v h) :
    ValVis_weak v (shift_val cutoff padding.length v)
      h (shift_heap cutoff padding h) := by
  intro n
  exact (valVis_self_shift_aux cutoff padding n h h_heap h_cutoff).1 v hv

/-! ## Policy shift-respecting predicate -/

/-- A policy is **shift-respecting** for a fixed `cutoff`/`padding` if its
    verdict is invariant under coordinated shifting of all of its inputs.
    This is the analog of `PolicyRespectsBisim` for shift-renaming
    (which differs from a length-preserving bisim). -/
def PolicyRespectsShift (cutoff : Nat) (padding : Heap) (p : BlackPolicy) : Prop :=
  ∀ (target : String) (idx : Nat) (env metaEnv : Env)
    (heap : Heap) (oldVal new : Val),
    cutoff ≤ heap.length →
    p { target := target, heap := heap, env := env,
        metaEnv := metaEnv, index := idx } oldVal new =
    p { target := target,
        heap := shift_heap cutoff padding heap,
        env := shift_env cutoff padding.length env,
        metaEnv := shift_env cutoff padding.length metaEnv,
        index := shift_idx cutoff padding.length idx }
      (shift_val cutoff padding.length oldVal)
      (shift_val cutoff padding.length new)

/-- A policy table is **shift-respecting** if every entry is. Used as a
    standing invariant: any `.installPolicy` substitutes a fresh policy
    drawn from `ptable`, and we maintain `PolicyRespectsShift`-of-current. -/
def PolicyTableRespectsShift (cutoff : Nat) (padding : Heap)
    (ptable : PolicyTable) : Prop :=
  ∀ (idx : Nat) p, ptable[idx]? = some p → PolicyRespectsShift cutoff padding p

/-! ## Shift commutativity for `applyPrim`

    Each primitive's per-prim helper commutes with shift, because
    shift_val preserves all constructors except `.closure` (which keeps
    the constructor and shifts the captured cenv). The arithmetic /
    comparison primitives only inspect `.num` / `.bool`, which are
    fixed by shift_val. The structural primitives (`cons`/`car`/`cdr`)
    work uniformly. -/

private theorem shift_mulConsList (cutoff offset : Nat) :
    ∀ (v : Val),
      mulConsList (shift_val cutoff offset v) = mulConsList v
  | .nilV => rfl
  | .cons (.num _) rest => by
      simp only [shift_val, mulConsList, shift_mulConsList cutoff offset rest]
  | .cons (.bool _) _ => rfl
  | .cons (.closure _ _ _) _ => rfl
  | .cons .nilV _ => rfl
  | .cons (.sym _) _ => rfl
  | .cons (.prim _) _ => rfl
  | .cons .builtinBaseApply _ => rfl
  | .cons (.cons _ _) _ => rfl
  | .num _ => rfl
  | .bool _ => rfl
  | .sym _ => rfl
  | .prim _ => rfl
  | .builtinBaseApply => rfl
  | .closure _ _ _ => rfl

private theorem shift_applyPrim (cutoff offset : Nat) (name : String) :
    ∀ (args : List Val),
      applyPrim name (shift_listVal cutoff offset args)
        = (applyPrim name args).map (shift_val cutoff offset) := by
  intro args
  -- shift_listVal is List.map shift_val (already proven).
  rw [shift_listVal_eq_map]
  -- Case on args structure for the relevant prims (1-arg, 2-arg shapes).
  -- Top-level dispatch is by string equality on `name`.
  unfold applyPrim
  -- Each branch handles one prim. We'll case-analyze args as needed.
  by_cases h_plus : name = "+"
  · subst h_plus
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
      first
      | (cases a <;> cases b <;>
         simp [applyPrim_plus, shift_val, List.map])
      | simp [applyPrim_plus, shift_val, List.map]
  · simp only [if_neg h_plus]
    by_cases h_minus : name = "-"
    · subst h_minus
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
        first
        | (cases a <;> cases b <;>
           simp [applyPrim_minus, shift_val, List.map])
        | simp [applyPrim_minus, shift_val, List.map]
    · simp only [if_neg h_minus]
      by_cases h_times : name = "*"
      · subst h_times
        rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
          first
          | (cases a <;> cases b <;>
             simp [applyPrim_times, shift_val, List.map])
          | simp [applyPrim_times, shift_val, List.map]
      · simp only [if_neg h_times]
        by_cases h_mul : name = "mul-list"
        · subst h_mul
          rcases args with _ | ⟨a, _ | _⟩
          · simp [applyPrim_mulList, List.map]
          · simp [applyPrim_mulList, List.map, shift_mulConsList cutoff offset a]
            cases mulConsList a <;> simp [shift_val]
          · simp [applyPrim_mulList, List.map]
        · simp only [if_neg h_mul]
          by_cases h_eq : name = "="
          · subst h_eq
            rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
              first
              | (cases a <;> cases b <;>
                 simp [applyPrim_eq, shift_val, List.map])
              | simp [applyPrim_eq, shift_val, List.map]
          · simp only [if_neg h_eq]
            by_cases h_numQ : name = "num?"
            · subst h_numQ
              rcases args with _ | ⟨a, _ | _⟩
              · simp [applyPrim_numQ, List.map]
              · cases a <;> simp [applyPrim_numQ, shift_val, List.map]
              · simp [applyPrim_numQ, List.map]
            · simp only [if_neg h_numQ]
              by_cases h_boolQ : name = "bool?"
              · subst h_boolQ
                rcases args with _ | ⟨a, _ | _⟩
                · simp [applyPrim_boolQ, List.map]
                · cases a <;> simp [applyPrim_boolQ, shift_val, List.map]
                · simp [applyPrim_boolQ, List.map]
              · simp only [if_neg h_boolQ]
                by_cases h_clQ : name = "closure?"
                · subst h_clQ
                  rcases args with _ | ⟨a, _ | _⟩
                  · simp [applyPrim_closureQ, List.map]
                  · cases a <;> simp [applyPrim_closureQ, shift_val, List.map]
                  · simp [applyPrim_closureQ, List.map]
                · simp only [if_neg h_clQ]
                  by_cases h_pQ : name = "prim?"
                  · subst h_pQ
                    rcases args with _ | ⟨a, _ | _⟩
                    · simp [applyPrim_primQ, List.map]
                    · cases a <;> simp [applyPrim_primQ, shift_val, List.map]
                    · simp [applyPrim_primQ, List.map]
                  · simp only [if_neg h_pQ]
                    by_cases h_cons : name = "cons"
                    · subst h_cons
                      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
                        simp [applyPrim_cons, shift_val, List.map]
                    · simp only [if_neg h_cons]
                      by_cases h_car : name = "car"
                      · subst h_car
                        rcases args with _ | ⟨a, _ | _⟩
                        · simp [applyPrim_car, List.map]
                        · cases a <;> simp [applyPrim_car, shift_val, List.map]
                        · simp [applyPrim_car, List.map]
                      · simp only [if_neg h_car]
                        by_cases h_cdr : name = "cdr"
                        · subst h_cdr
                          rcases args with _ | ⟨a, _ | _⟩
                          · simp [applyPrim_cdr, List.map]
                          · cases a <;> simp [applyPrim_cdr, shift_val, List.map]
                          · simp [applyPrim_cdr, List.map]
                        · simp only [if_neg h_cdr]
                          by_cases h_null : name = "null?"
                          · subst h_null
                            rcases args with _ | ⟨a, _ | _⟩
                            · simp [applyPrim_nullQ, List.map]
                            · cases a <;> simp [applyPrim_nullQ, shift_val, List.map]
                            · simp [applyPrim_nullQ, List.map]
                          · simp only [if_neg h_null]
                            simp

/-! ## Heap monotonicity (single-side)

    `eval / evalList / applyVia / applyDirect` only grow the heap.
    Used by `shift_respect` to thread `cutoff ≤ s.heap.length` through
    inner IH calls. -/

/-- Length grown by an `allocStep` foldl: exactly `lst.length` cells. -/
private theorem allocStep_foldl_length :
    ∀ (lst : List (Val × String)) (h : Heap) (cenv : Env),
      (lst.foldl allocStep (h, cenv)).1.length = h.length + lst.length
  | [], h, _ => by simp [List.foldl]
  | hd :: tl, h, cenv => by
      simp only [List.foldl, allocStep, Heap.alloc]
      rw [allocStep_foldl_length tl (h ++ [hd.1]) (.cons hd.2 h.length cenv)]
      simp [List.length_append]; omega

/-- The fold's heap monotonically extends `h`. -/
private theorem allocStep_foldl_heap_prefix :
    ∀ (lst : List (Val × String)) (h : Heap) (cenv : Env),
      ∃ ext, (lst.foldl allocStep (h, cenv)).1 = h ++ ext
  | [], h, _ => ⟨[], by simp [List.foldl]⟩
  | hd :: tl, h, cenv => by
      simp only [List.foldl, allocStep, Heap.alloc]
      obtain ⟨ext, h_ext⟩ :=
        allocStep_foldl_heap_prefix tl (h ++ [hd.1]) (.cons hd.2 h.length cenv)
      exact ⟨[hd.1] ++ ext, by rw [h_ext]; simp [List.append_assoc]⟩

/-- Shift commutes with the `allocStep` foldl: applying the fold over
    a shifted-args / shifted-cenv on a shifted heap gives the shift of
    applying the fold on the unshifted heap. The shifted-args list is
    `lst` with the value component shifted; the param strings are
    unchanged. -/
private theorem allocStep_foldl_shift (cutoff : Nat) (padding : Heap) :
    ∀ (lst : List (Val × String)) (h : Heap) (cenv : Env),
      cutoff ≤ h.length →
      let lst_b : List (Val × String) :=
        lst.map (fun vp => (shift_val cutoff padding.length vp.1, vp.2))
      let result_a := lst.foldl allocStep (h, cenv)
      let result_b := lst_b.foldl allocStep
        (shift_heap cutoff padding h, shift_env cutoff padding.length cenv)
      result_b.1 = shift_heap cutoff padding result_a.1 ∧
      result_b.2 = shift_env cutoff padding.length result_a.2
  | [], h, cenv, _h_cutoff => by simp [List.foldl]
  | (v, p) :: tl, h, cenv, h_cutoff => by
      simp only [List.foldl, allocStep, Heap.alloc, List.map_cons]
      -- After 1 step on side A: (h ++ [v], .cons p h.length cenv)
      -- After 1 step on side B: (shift_heap h ++ [shift_val v], .cons p (shift_heap h).length (shift_env cenv))
      have h_len_b : (shift_heap cutoff padding h).length = h.length + padding.length := by
        rw [shift_heap_length]
      -- Rewrite: shift_heap h ++ [shift_val v] = shift_heap (h ++ [v]).
      have h_heap_eq :
          shift_heap cutoff padding h ++ [shift_val cutoff padding.length v]
            = shift_heap cutoff padding (h ++ [v]) := by
        rw [shift_heap_append cutoff padding h [v] h_cutoff]
        rfl
      -- shift_idx h.length = h.length + padding.length (since h.length ≥ cutoff).
      have h_idx_eq :
          shift_idx cutoff padding.length h.length = h.length + padding.length := by
        unfold shift_idx
        rw [if_neg (by omega : ¬ h.length < cutoff)]
      -- shift_env (.cons p h.length cenv) = .cons p (shift_idx h.length) (shift_env cenv)
      have h_env_eq :
          shift_env cutoff padding.length (.cons p h.length cenv)
            = .cons p (h.length + padding.length) (shift_env cutoff padding.length cenv) := by
        simp only [shift_env, ← h_idx_eq]
      have h_cutoff_ext : cutoff ≤ (h ++ [v]).length := by
        rw [List.length_append]; omega
      -- Apply IH to the tail with the new state.
      have h_ih := allocStep_foldl_shift cutoff padding tl
        (h ++ [v]) (.cons p h.length cenv) h_cutoff_ext
      simp only at h_ih
      -- Need to rewrite side B's foldl-tail to match the IH.
      rw [show (shift_heap cutoff padding h ++ [shift_val cutoff padding.length v],
               Env.cons p (shift_heap cutoff padding h).length
                 (shift_env cutoff padding.length cenv))
            = (shift_heap cutoff padding (h ++ [v]),
               shift_env cutoff padding.length (.cons p h.length cenv)) from by
        rw [h_heap_eq, h_env_eq, h_len_b]]
      exact h_ih

private def HeapMonoStmt (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (exp : Expr) (env metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    eval n ptable exp env metaEnv s = some (r, s') →
    s.heap.length ≤ s'.heap.length) ∧
  (∀ (ptable : PolicyTable) (exps : List Expr) (env metaEnv : Env)
     (s : RunState) (rs : List Val) (s' : RunState),
    evalList n ptable exps env metaEnv s = some (rs, s') →
    s.heap.length ≤ s'.heap.length) ∧
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    applyVia n ptable op args metaEnv s = some (r, s') →
    s.heap.length ≤ s'.heap.length) ∧
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    applyDirect n ptable op args metaEnv s = some (r, s') →
    s.heap.length ≤ s'.heap.length)

private theorem heap_mono : ∀ n, HeapMonoStmt n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ h; simp [eval] at h
      · intro _ _ _ _ _ _ _ h; simp [evalList] at h
      · intro _ _ _ _ _ _ _ h; simp [applyVia] at h
      · intro _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable exp env metaEnv s r s' h_eval
        cases exp with
        | num i =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
        | bool b =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
        | quote v =>
            simp only [eval] at h_eval
            split at h_eval
            · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
            · simp at h_eval
        | var x =>
            simp only [eval] at h_eval
            cases hl : env.lookup x with
            | none => rw [hl] at h_eval; simp at h_eval
            | some idx =>
                rw [hl] at h_eval
                simp only at h_eval
                cases hp : s.heap[idx]? with
                | none => rw [hp] at h_eval; simp at h_eval
                | some v =>
                    rw [hp] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
        | lam ps body =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
        | installPolicy idx =>
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
            | some np =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s
                show s.heap.length ≤ ({s with policy := np} : RunState).heap.length
                exact Nat.le_refl _
        | ifte c t e =>
            simp only [eval] at h_eval
            cases hc : eval k ptable c env metaEnv s with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv, s_c⟩ := pr
                rw [hc] at h_eval
                have h1 : s.heap.length ≤ s_c.heap.length :=
                  ih_eval ptable c env metaEnv s cv s_c hc
                by_cases hcv : cv = .bool false
                · subst hcv
                  simp only at h_eval
                  have h2 : s_c.heap.length ≤ s'.heap.length :=
                    ih_eval ptable e env metaEnv s_c r s' h_eval
                  exact Nat.le_trans h1 h2
                · have h_eval_t : eval k ptable t env metaEnv s_c = some (r, s') := by
                    cases cv with
                    | bool b =>
                        cases b with
                        | false => exact absurd rfl hcv
                        | true => exact h_eval
                    | num _ => exact h_eval
                    | nilV => exact h_eval
                    | cons _ _ => exact h_eval
                    | sym _ => exact h_eval
                    | closure _ _ _ => exact h_eval
                    | prim _ => exact h_eval
                    | builtinBaseApply => exact h_eval
                  have h2 : s_c.heap.length ≤ s'.heap.length :=
                    ih_eval ptable t env metaEnv s_c r s' h_eval_t
                  exact Nat.le_trans h1 h2
        | app exps =>
            cases exps with
            | nil => simp only [eval] at h_eval; exact absurd h_eval (by simp)
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable f env metaEnv s with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv, s1⟩ := pr
                    rw [hf] at h_eval
                    simp only at h_eval
                    have h1 : s.heap.length ≤ s1.heap.length :=
                      ih_eval ptable f env metaEnv s fv s1 hf
                    cases ha : evalList k ptable args env metaEnv s1 with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs, s2⟩ := pr2
                        rw [ha] at h_eval
                        simp only at h_eval
                        have h2 : s1.heap.length ≤ s2.heap.length :=
                          ih_evalList ptable args env metaEnv s1 avs s2 ha
                        have h3 : s2.heap.length ≤ s'.heap.length :=
                          ih_applyVia ptable fv avs metaEnv s2 r s' h_eval
                        exact Nat.le_trans h1 (Nat.le_trans h2 h3)
        | primApp f args =>
            simp only [eval] at h_eval
            cases hf : eval k ptable f env metaEnv s with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv, s1⟩ := pr
                rw [hf] at h_eval
                simp only at h_eval
                have h1 : s.heap.length ≤ s1.heap.length :=
                  ih_eval ptable f env metaEnv s fv s1 hf
                cases ha : evalList k ptable args env metaEnv s1 with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs, s2⟩ := pr2
                    rw [ha] at h_eval
                    simp only at h_eval
                    have h2 : s1.heap.length ≤ s2.heap.length :=
                      ih_evalList ptable args env metaEnv s1 avs s2 ha
                    have h3 : s2.heap.length ≤ s'.heap.length :=
                      ih_applyDirect ptable fv avs metaEnv s2 r s' h_eval
                    exact Nat.le_trans h1 (Nat.le_trans h2 h3)
        | set x e =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h1 : s.heap.length ≤ s1.heap.length :=
                  ih_eval ptable e env metaEnv s v s1 he
                cases hl : env.lookup x with
                | none => rw [hl] at h_eval; simp at h_eval
                | some idx =>
                    rw [hl] at h_eval
                    simp only at h_eval
                    split at h_eval
                    · -- isMetaMutation = true branch
                      cases hp : s1.heap[idx]? with
                      | none => rw [hp] at h_eval; simp at h_eval
                      | some oldVal =>
                          rw [hp] at h_eval
                          simp only at h_eval
                          split at h_eval
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨_, h_s⟩ := h_eval; subst h_s
                            show s.heap.length ≤
                              ({s1 with heap := s1.heap.update idx v} : RunState).heap.length
                            rw [Heap.update_length]; exact h1
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact h1
                    · -- isMetaMutation = false branch
                      simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                      obtain ⟨_, h_s⟩ := h_eval; subst h_s
                      show s.heap.length ≤
                        ({s1 with heap := s1.heap.update idx v} : RunState).heap.length
                      rw [Heap.update_length]; exact h1
        | em body =>
            simp only [eval] at h_eval
            exact ih_eval ptable body metaEnv metaEnv s r s' h_eval
        | letE x e body =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h1 : s.heap.length ≤ s1.heap.length :=
                  ih_eval ptable e env metaEnv s v s1 he
                have h2 :
                    ({s1 with heap := s1.heap ++ [v]} : RunState).heap.length
                      ≤ s'.heap.length := by
                  apply ih_eval ptable body (.cons x s1.heap.length env) metaEnv
                    {s1 with heap := s1.heap ++ [v]} r s'
                  exact h_eval
                have h_app : s1.heap.length
                    ≤ ({s1 with heap := s1.heap ++ [v]} : RunState).heap.length := by
                  show s1.heap.length ≤ (s1.heap ++ [v]).length
                  rw [List.length_append]; omega
                exact Nat.le_trans h1 (Nat.le_trans h_app h2)
        | seq exps =>
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
            | cons e rest =>
                cases rest with
                | nil =>
                    simp only [eval] at h_eval
                    exact ih_eval ptable e env metaEnv s r s' h_eval
                | cons e2 rest2 =>
                    simp only [eval] at h_eval
                    cases he : eval k ptable e env metaEnv s with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨v, s1⟩ := pr
                        rw [he] at h_eval
                        simp only at h_eval
                        have h1 : s.heap.length ≤ s1.heap.length :=
                          ih_eval ptable e env metaEnv s v s1 he
                        have h2 : s1.heap.length ≤ s'.heap.length :=
                          ih_eval ptable (.seq (e2 :: rest2)) env metaEnv s1 r s' h_eval
                        exact Nat.le_trans h1 h2
      · -- evalList (k+1)
        intro ptable exps env metaEnv s rs s' h_eval
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact Nat.le_refl _
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h1 : s.heap.length ≤ s1.heap.length :=
                  ih_eval ptable e env metaEnv s v s1 he
                cases hr : evalList k ptable rest env metaEnv s1 with
                | none => rw [hr] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨vs, s2⟩ := pr2
                    rw [hr] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_s⟩ := h_eval; subst h_s
                    have h2 : s1.heap.length ≤ s2.heap.length :=
                      ih_evalList ptable rest env metaEnv s1 vs s2 hr
                    exact Nat.le_trans h1 h2
      · -- applyVia (k+1)
        intro ptable op args metaEnv s r s' h_app
        simp only [applyVia] at h_app
        cases hl : metaEnv.lookup "base-apply" with
        | none =>
            rw [hl] at h_app
            exact ih_applyDirect ptable op args metaEnv s r s' h_app
        | some idx =>
            rw [hl] at h_app
            simp only at h_app
            cases hp : s.heap[idx]? with
            | none => rw [hp] at h_app; simp at h_app
            | some baseApply =>
                rw [hp] at h_app
                cases baseApply with
                | builtinBaseApply =>
                    simp only at h_app
                    exact ih_applyDirect ptable op args metaEnv s r s' h_app
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
                    simp only at h_app
                    exact ih_applyDirect ptable _ [op, listToVal args] metaEnv s r s' h_app
      · -- applyDirect (k+1)
        intro ptable op args metaEnv s r s' h_app
        simp only [applyDirect] at h_app
        cases op with
        | num _ => exact absurd h_app (by simp)
        | bool _ => exact absurd h_app (by simp)
        | nilV => exact absurd h_app (by simp)
        | sym _ => exact absurd h_app (by simp)
        | cons _ _ => exact absurd h_app (by simp)
        | prim name =>
            simp only at h_app
            cases hp : applyPrim name args with
            | none => rw [hp] at h_app; simp at h_app
            | some v =>
                rw [hp] at h_app
                simp only [Option.some.injEq, Prod.mk.injEq] at h_app
                obtain ⟨_, h_s⟩ := h_app; subst h_s; exact Nat.le_refl _
        | builtinBaseApply =>
            simp only at h_app
            cases args with
            | nil => simp at h_app
            | cons a as =>
                cases as with
                | nil => simp at h_app
                | cons o rest =>
                    cases rest with
                    | nil =>
                        simp only at h_app
                        cases hv : valToList o with
                        | none => rw [hv] at h_app; simp at h_app
                        | some operands =>
                            rw [hv] at h_app
                            exact ih_applyDirect ptable a operands metaEnv s r s' h_app
                    | cons _ _ => simp at h_app
        | closure ps body cenv =>
            simp only at h_app
            split at h_app
            · simp at h_app
            · rename_i h_len
              -- Inline lambda is definitionally `allocStep`.
              -- The fold yields (h', env') with h'.length = s.heap.length + (args.zip ps).length.
              have h_foldl_len :
                  ((args.zip ps).foldl allocStep (s.heap, cenv)).1.length
                    = s.heap.length + (args.zip ps).length :=
                allocStep_foldl_length (args.zip ps) s.heap cenv
              have h1 : s.heap.length
                  ≤ ((args.zip ps).foldl allocStep (s.heap, cenv)).1.length := by
                rw [h_foldl_len]; omega
              have h2 :
                  ({s with heap :=
                    ((args.zip ps).foldl allocStep (s.heap, cenv)).1} : RunState).heap.length
                    ≤ s'.heap.length :=
                ih_eval ptable body
                  ((args.zip ps).foldl allocStep (s.heap, cenv)).2 metaEnv
                  {s with heap :=
                    ((args.zip ps).foldl allocStep (s.heap, cenv)).1} r s' h_app
              exact Nat.le_trans h1 h2

/-! ## Policy-shift-respecting preservation

    The policy can only change via `.installPolicy`, which substitutes
    a fresh policy from `ptable`. So if `ptable` is shift-respecting
    everywhere, `PolicyRespectsShift` is preserved across any
    eval/evalList/applyVia/applyDirect call. -/

private def PolicyShiftPreservedStmt (cutoff : Nat) (padding : Heap)
    (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (exp : Expr) (env metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    eval n ptable exp env metaEnv s = some (r, s') →
    PolicyRespectsShift cutoff padding s'.policy) ∧
  (∀ (ptable : PolicyTable) (exps : List Expr) (env metaEnv : Env)
     (s : RunState) (rs : List Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    evalList n ptable exps env metaEnv s = some (rs, s') →
    PolicyRespectsShift cutoff padding s'.policy) ∧
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    applyVia n ptable op args metaEnv s = some (r, s') →
    PolicyRespectsShift cutoff padding s'.policy) ∧
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    applyDirect n ptable op args metaEnv s = some (r, s') →
    PolicyRespectsShift cutoff padding s'.policy)

private theorem policy_shift_preserved (cutoff : Nat) (padding : Heap) :
    ∀ n, PolicyShiftPreservedStmt cutoff padding n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ _ h; simp [eval] at h
      · intro _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
      · intro _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
      · intro _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable exp env metaEnv s r s' hresp_pt hresp_init h_eval
        cases exp with
        | num i =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
        | bool b =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
        | quote v =>
            simp only [eval] at h_eval
            split at h_eval
            · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
            · simp at h_eval
        | var x =>
            simp only [eval] at h_eval
            cases hl : env.lookup x with
            | none => rw [hl] at h_eval; simp at h_eval
            | some idx =>
                rw [hl] at h_eval
                simp only at h_eval
                cases hp : s.heap[idx]? with
                | none => rw [hp] at h_eval; simp at h_eval
                | some v =>
                    rw [hp] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
        | lam ps body =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
        | installPolicy idx =>
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
            | some np =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s
                show PolicyRespectsShift cutoff padding ({s with policy := np} : RunState).policy
                exact hresp_pt idx np hp
        | ifte c t e =>
            simp only [eval] at h_eval
            cases hc : eval k ptable c env metaEnv s with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv, s_c⟩ := pr
                rw [hc] at h_eval
                have h_c := ih_eval ptable c env metaEnv s cv s_c hresp_pt hresp_init hc
                by_cases hcv : cv = .bool false
                · subst hcv
                  simp only at h_eval
                  exact ih_eval ptable e env metaEnv s_c r s' hresp_pt h_c h_eval
                · have h_eval_t : eval k ptable t env metaEnv s_c = some (r, s') := by
                    cases cv with
                    | bool b => cases b with
                      | false => exact absurd rfl hcv
                      | true => exact h_eval
                    | num _ => exact h_eval
                    | nilV => exact h_eval
                    | cons _ _ => exact h_eval
                    | sym _ => exact h_eval
                    | closure _ _ _ => exact h_eval
                    | prim _ => exact h_eval
                    | builtinBaseApply => exact h_eval
                  exact ih_eval ptable t env metaEnv s_c r s' hresp_pt h_c h_eval_t
        | app exps =>
            cases exps with
            | nil => simp only [eval] at h_eval; exact absurd h_eval (by simp)
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable f env metaEnv s with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv, s1⟩ := pr
                    rw [hf] at h_eval
                    simp only at h_eval
                    have h1 := ih_eval ptable f env metaEnv s fv s1 hresp_pt hresp_init hf
                    cases ha : evalList k ptable args env metaEnv s1 with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs, s2⟩ := pr2
                        rw [ha] at h_eval
                        simp only at h_eval
                        have h2 := ih_evalList ptable args env metaEnv s1 avs s2
                          hresp_pt h1 ha
                        exact ih_applyVia ptable fv avs metaEnv s2 r s' hresp_pt h2 h_eval
        | primApp f args =>
            simp only [eval] at h_eval
            cases hf : eval k ptable f env metaEnv s with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv, s1⟩ := pr
                rw [hf] at h_eval
                simp only at h_eval
                have h1 := ih_eval ptable f env metaEnv s fv s1 hresp_pt hresp_init hf
                cases ha : evalList k ptable args env metaEnv s1 with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs, s2⟩ := pr2
                    rw [ha] at h_eval
                    simp only at h_eval
                    have h2 := ih_evalList ptable args env metaEnv s1 avs s2
                      hresp_pt h1 ha
                    exact ih_applyDirect ptable fv avs metaEnv s2 r s' hresp_pt h2 h_eval
        | set x e =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e := ih_eval ptable e env metaEnv s v s1 hresp_pt hresp_init he
                cases hl : env.lookup x with
                | none => rw [hl] at h_eval; simp at h_eval
                | some idx =>
                    rw [hl] at h_eval
                    simp only at h_eval
                    split at h_eval
                    · cases hp : s1.heap[idx]? with
                      | none => rw [hp] at h_eval; simp at h_eval
                      | some oldVal =>
                          rw [hp] at h_eval
                          simp only at h_eval
                          split at h_eval
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨_, h_s⟩ := h_eval; subst h_s
                            show PolicyRespectsShift cutoff padding
                              ({s1 with heap := s1.heap.update idx v} : RunState).policy
                            exact h_e
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact h_e
                    · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                      obtain ⟨_, h_s⟩ := h_eval; subst h_s
                      show PolicyRespectsShift cutoff padding
                        ({s1 with heap := s1.heap.update idx v} : RunState).policy
                      exact h_e
        | em body =>
            simp only [eval] at h_eval
            exact ih_eval ptable body metaEnv metaEnv s r s' hresp_pt hresp_init h_eval
        | letE x e body =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e := ih_eval ptable e env metaEnv s v s1 hresp_pt hresp_init he
                exact ih_eval ptable body (.cons x s1.heap.length env) metaEnv
                  {s1 with heap := s1.heap ++ [v]} r s' hresp_pt h_e h_eval
        | seq exps =>
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
            | cons e rest =>
                cases rest with
                | nil =>
                    simp only [eval] at h_eval
                    exact ih_eval ptable e env metaEnv s r s' hresp_pt hresp_init h_eval
                | cons e2 rest2 =>
                    simp only [eval] at h_eval
                    cases he : eval k ptable e env metaEnv s with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨v, s1⟩ := pr
                        rw [he] at h_eval
                        simp only at h_eval
                        have h_e := ih_eval ptable e env metaEnv s v s1 hresp_pt hresp_init he
                        exact ih_eval ptable (.seq (e2 :: rest2)) env metaEnv s1 r s'
                          hresp_pt h_e h_eval
      · -- evalList (k+1)
        intro ptable exps env metaEnv s rs s' hresp_pt hresp_init h_eval
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_s⟩ := h_eval; subst h_s; exact hresp_init
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e := ih_eval ptable e env metaEnv s v s1 hresp_pt hresp_init he
                cases hr : evalList k ptable rest env metaEnv s1 with
                | none => rw [hr] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨vs, s2⟩ := pr2
                    rw [hr] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_s⟩ := h_eval; subst h_s
                    exact ih_evalList ptable rest env metaEnv s1 vs s2 hresp_pt h_e hr
      · -- applyVia (k+1)
        intro ptable op args metaEnv s r s' hresp_pt hresp_init h_app
        simp only [applyVia] at h_app
        cases hl : metaEnv.lookup "base-apply" with
        | none =>
            rw [hl] at h_app
            exact ih_applyDirect ptable op args metaEnv s r s' hresp_pt hresp_init h_app
        | some idx =>
            rw [hl] at h_app
            simp only at h_app
            cases hp : s.heap[idx]? with
            | none => rw [hp] at h_app; simp at h_app
            | some baseApply =>
                rw [hp] at h_app
                cases baseApply with
                | builtinBaseApply =>
                    simp only at h_app
                    exact ih_applyDirect ptable op args metaEnv s r s' hresp_pt hresp_init h_app
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
                    simp only at h_app
                    exact ih_applyDirect ptable _ [op, listToVal args] metaEnv s r s'
                      hresp_pt hresp_init h_app
      · -- applyDirect (k+1)
        intro ptable op args metaEnv s r s' hresp_pt hresp_init h_app
        simp only [applyDirect] at h_app
        cases op with
        | num _ => exact absurd h_app (by simp)
        | bool _ => exact absurd h_app (by simp)
        | nilV => exact absurd h_app (by simp)
        | sym _ => exact absurd h_app (by simp)
        | cons _ _ => exact absurd h_app (by simp)
        | prim name =>
            simp only at h_app
            cases hp : applyPrim name args with
            | none => rw [hp] at h_app; simp at h_app
            | some v =>
                rw [hp] at h_app
                simp only [Option.some.injEq, Prod.mk.injEq] at h_app
                obtain ⟨_, h_s⟩ := h_app; subst h_s; exact hresp_init
        | builtinBaseApply =>
            simp only at h_app
            cases args with
            | nil => simp at h_app
            | cons a as =>
                cases as with
                | nil => simp at h_app
                | cons o rest =>
                    cases rest with
                    | nil =>
                        simp only at h_app
                        cases hv : valToList o with
                        | none => rw [hv] at h_app; simp at h_app
                        | some operands =>
                            rw [hv] at h_app
                            exact ih_applyDirect ptable a operands metaEnv s r s'
                              hresp_pt hresp_init h_app
                    | cons _ _ => simp at h_app
        | closure ps body cenv =>
            simp only at h_app
            split at h_app
            · simp at h_app
            · -- The fold doesn't change policy; eval body may.
              exact ih_eval ptable body
                ((args.zip ps).foldl allocStep (s.heap, cenv)).2 metaEnv
                {s with heap := ((args.zip ps).foldl allocStep (s.heap, cenv)).1} r s'
                hresp_pt hresp_init h_app

/-! ## Joint shift-respect theorem (Option A's central claim)

    `eval / evalList / applyVia / applyDirect` all *commute* with shift:
    running on shifted inputs gives the shifted result. By joint mutual
    induction on fuel. Each case is a syntactic check using the shift-
    commutativity helpers proved above. -/

/-- Joint statement for the shift-respect theorem. The policy
    hypotheses (`PolicyTableRespectsShift` on `ptable`,
    `PolicyRespectsShift` on `s.policy`) are needed by the `.set`
    case; for inner IH calls they are supplied by passing through
    `hresp_pt` and using `policy_shift_preserved` to derive the
    inner-state hypothesis. -/
private def ShiftRespectStmt (cutoff : Nat) (padding : Heap) (n : Nat) : Prop :=
  let offset := padding.length
  -- eval respects shift
  (∀ (ptable : PolicyTable) (exp : Expr) (env metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    cutoff ≤ s.heap.length →
    eval n ptable exp env metaEnv s = some (r, s') →
    eval n ptable exp (shift_env cutoff offset env) (shift_env cutoff offset metaEnv)
         (shift_state cutoff padding s)
      = some (shift_val cutoff offset r, shift_state cutoff padding s')) ∧
  -- evalList respects shift
  (∀ (ptable : PolicyTable) (exps : List Expr) (env metaEnv : Env)
     (s : RunState) (rs : List Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    cutoff ≤ s.heap.length →
    evalList n ptable exps env metaEnv s = some (rs, s') →
    evalList n ptable exps (shift_env cutoff offset env)
             (shift_env cutoff offset metaEnv) (shift_state cutoff padding s)
      = some (shift_listVal cutoff offset rs, shift_state cutoff padding s')) ∧
  -- applyVia respects shift
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    cutoff ≤ s.heap.length →
    applyVia n ptable op args metaEnv s = some (r, s') →
    applyVia n ptable (shift_val cutoff offset op)
              (shift_listVal cutoff offset args)
              (shift_env cutoff offset metaEnv) (shift_state cutoff padding s)
      = some (shift_val cutoff offset r, shift_state cutoff padding s')) ∧
  -- applyDirect respects shift
  (∀ (ptable : PolicyTable) (op : Val) (args : List Val) (metaEnv : Env)
     (s : RunState) (r : Val) (s' : RunState),
    PolicyTableRespectsShift cutoff padding ptable →
    PolicyRespectsShift cutoff padding s.policy →
    cutoff ≤ s.heap.length →
    applyDirect n ptable op args metaEnv s = some (r, s') →
    applyDirect n ptable (shift_val cutoff offset op)
                (shift_listVal cutoff offset args)
                (shift_env cutoff offset metaEnv) (shift_state cutoff padding s)
      = some (shift_val cutoff offset r, shift_state cutoff padding s'))

private theorem shift_respect (cutoff : Nat) (padding : Heap) :
    ∀ n, ShiftRespectStmt cutoff padding n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ _ _ h
        exact absurd h (by unfold eval; simp)
      · intro _ _ _ _ _ _ _ _ _ _ h
        exact absurd h (by unfold evalList; simp)
      · intro _ _ _ _ _ _ _ _ _ _ h
        exact absurd h (by unfold applyVia; simp)
      · intro _ _ _ _ _ _ _ _ _ _ h
        exact absurd h (by unfold applyDirect; simp)
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      have ih_pp := policy_shift_preserved cutoff padding k
      obtain ⟨pp_eval, pp_evalList, pp_applyVia, pp_applyDirect⟩ := ih_pp
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable exp env metaEnv s r s' hresp_pt hresp_init h_cutoff h_eval
        cases exp with
        | num i =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            simp [eval, shift_val]
        | bool b =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            simp [eval, shift_val]
        | quote v =>
            simp only [eval] at h_eval
            split at h_eval
            · rename_i h_closed
              simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨h_r, h_s⟩ := h_eval
              subst h_r; subst h_s
              -- shift_val on closedValB v is v itself.
              have h_shift_v : shift_val cutoff padding.length v = v :=
                shift_val_id cutoff padding.length (closedValB_AllBelow cutoff v h_closed)
              rw [h_shift_v]
              simp [eval, h_closed]
            · simp at h_eval
        | var x =>
            simp only [eval] at h_eval
            cases hl : env.lookup x with
            | none => rw [hl] at h_eval; simp at h_eval
            | some idx =>
                rw [hl] at h_eval
                simp only at h_eval
                cases hp : s.heap[idx]? with
                | none => rw [hp] at h_eval; simp at h_eval
                | some v =>
                    rw [hp] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_r, h_s⟩ := h_eval
                    subst h_r; subst h_s
                    simp only [eval]
                    rw [shift_env_lookup cutoff padding.length env x idx hl]
                    simp only
                    -- (shift_state s).heap = shift_heap s.heap.
                    show (match (shift_heap cutoff padding s.heap)[shift_idx cutoff padding.length idx]?
                          with | some v_b => some (v_b, shift_state cutoff padding s)
                               | none     => none)
                       = some (shift_val cutoff padding.length v, shift_state cutoff padding s)
                    rw [shift_heap_getElem? cutoff padding s.heap idx h_cutoff, hp]
                    rfl
        | lam ps body =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            simp [eval, shift_val]
        | installPolicy idx =>
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                simp [eval, hp, shift_val]
            | some newPolicy =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                simp only [eval, hp]
                show some (.bool true,
                            { (shift_state cutoff padding s) with policy := newPolicy })
                  = some (shift_val cutoff padding.length (.bool true),
                          shift_state cutoff padding { s with policy := newPolicy })
                simp [shift_val, shift_state, shift_heap]
        | seq exps =>
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_s⟩ := h_eval
                subst h_r; subst h_s
                simp [eval, shift_val]
            | cons e rest =>
                cases rest with
                | nil =>
                    simp only [eval] at h_eval
                    have h_eval_b := ih_eval ptable e env metaEnv s r s'
                      hresp_pt hresp_init h_cutoff h_eval
                    simp [eval, h_eval_b]
                | cons e2 rest2 =>
                    simp only [eval] at h_eval
                    cases he : eval k ptable e env metaEnv s with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨v_e, s_inner⟩ := pr
                        rw [he] at h_eval
                        simp only at h_eval
                        have h_eval_e_b := ih_eval ptable e env metaEnv s v_e s_inner
                          hresp_pt hresp_init h_cutoff he
                        have h_mono := (heap_mono k).1 ptable e env metaEnv s v_e s_inner he
                        have h_cutoff_inner : cutoff ≤ s_inner.heap.length :=
                          Nat.le_trans h_cutoff h_mono
                        have h_pol_inner :=
                          pp_eval ptable e env metaEnv s v_e s_inner hresp_pt hresp_init he
                        have h_eval_seq_b := ih_eval ptable (.seq (e2 :: rest2))
                          env metaEnv s_inner r s'
                          hresp_pt h_pol_inner h_cutoff_inner h_eval
                        simp [eval, h_eval_e_b, h_eval_seq_b]
        | em body =>
            simp only [eval] at h_eval
            have h_b :=
              ih_eval ptable body metaEnv metaEnv s r s' hresp_pt hresp_init h_cutoff h_eval
            simp [eval, h_b]
        | ifte c t e =>
            simp only [eval] at h_eval
            cases hc : eval k ptable c env metaEnv s with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv, s_c⟩ := pr
                rw [hc] at h_eval
                have h_c_b := ih_eval ptable c env metaEnv s cv s_c
                  hresp_pt hresp_init h_cutoff hc
                have h_mono_c :=
                  (heap_mono k).1 ptable c env metaEnv s cv s_c hc
                have h_cutoff_c : cutoff ≤ s_c.heap.length :=
                  Nat.le_trans h_cutoff h_mono_c
                have h_pol_c :=
                  pp_eval ptable c env metaEnv s cv s_c hresp_pt hresp_init hc
                by_cases hcv : cv = .bool false
                · subst hcv
                  simp only at h_eval
                  have h_e_b :=
                    ih_eval ptable e env metaEnv s_c r s'
                      hresp_pt h_pol_c h_cutoff_c h_eval
                  show eval (k+1) ptable (.ifte c t e) _ _ _
                    = some (shift_val cutoff padding.length r,
                            shift_state cutoff padding s')
                  simp only [eval, h_c_b]
                  show (match (some (shift_val cutoff padding.length (.bool false),
                                     shift_state cutoff padding s_c)) with
                        | some (.bool false, s') =>
                            eval k ptable e (shift_env cutoff padding.length env)
                              (shift_env cutoff padding.length metaEnv) s'
                        | some (_, s') =>
                            eval k ptable t (shift_env cutoff padding.length env)
                              (shift_env cutoff padding.length metaEnv) s'
                        | none => none)
                       = some (shift_val cutoff padding.length r,
                               shift_state cutoff padding s')
                  simp only [shift_val]
                  exact h_e_b
                · have h_eval_t : eval k ptable t env metaEnv s_c = some (r, s') := by
                    cases cv with
                    | bool b =>
                        cases b with
                        | false => exact absurd rfl hcv
                        | true => exact h_eval
                    | num _ => exact h_eval
                    | nilV => exact h_eval
                    | cons _ _ => exact h_eval
                    | sym _ => exact h_eval
                    | closure _ _ _ => exact h_eval
                    | prim _ => exact h_eval
                    | builtinBaseApply => exact h_eval
                  have h_t_b :=
                    ih_eval ptable t env metaEnv s_c r s'
                      hresp_pt h_pol_c h_cutoff_c h_eval_t
                  show eval (k+1) ptable (.ifte c t e) _ _ _
                    = some (shift_val cutoff padding.length r,
                            shift_state cutoff padding s')
                  simp only [eval, h_c_b]
                  -- shift_val of cv is not .bool false (since cv ≠ .bool false).
                  cases cv with
                  | bool b =>
                      cases b with
                      | false => exact absurd rfl hcv
                      | true => simp only [shift_val]; exact h_t_b
                  | num _ => simp only [shift_val]; exact h_t_b
                  | nilV => simp only [shift_val]; exact h_t_b
                  | cons _ _ => simp only [shift_val]; exact h_t_b
                  | sym _ => simp only [shift_val]; exact h_t_b
                  | closure _ _ _ => simp only [shift_val]; exact h_t_b
                  | prim _ => simp only [shift_val]; exact h_t_b
                  | builtinBaseApply => simp only [shift_val]; exact h_t_b
        | letE x e body =>
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_e, s_inner⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e_b := ih_eval ptable e env metaEnv s v_e s_inner
                  hresp_pt hresp_init h_cutoff he
                have h_mono_e :=
                  (heap_mono k).1 ptable e env metaEnv s v_e s_inner he
                have h_cutoff_inner : cutoff ≤ s_inner.heap.length :=
                  Nat.le_trans h_cutoff h_mono_e
                have h_pol_inner :=
                  pp_eval ptable e env metaEnv s v_e s_inner hresp_pt hresp_init he
                have h_cutoff_alloc :
                    cutoff ≤ (s_inner.heap ++ [v_e]).length := by
                  rw [List.length_append]; omega
                -- Policy of the allocated state is same as s_inner (no policy change).
                have h_pol_alloc :
                    PolicyRespectsShift cutoff padding
                      ({s_inner with heap := s_inner.heap ++ [v_e]} : RunState).policy :=
                  h_pol_inner
                have h_body_b := ih_eval ptable body
                  (.cons x s_inner.heap.length env) metaEnv
                  {s_inner with heap := s_inner.heap ++ [v_e]} r s'
                  hresp_pt h_pol_alloc h_cutoff_alloc h_eval
                show eval (k+1) ptable (.letE x e body) _ _ _
                  = some (shift_val cutoff padding.length r,
                          shift_state cutoff padding s')
                simp only [eval, h_e_b]
                -- Goal: match some (shift_val v_e, shift_state s_inner) with ...
                show
                  (let (h'', idx) :=
                    (shift_state cutoff padding s_inner).heap.alloc
                      (shift_val cutoff padding.length v_e)
                  eval k ptable body
                    (.cons x idx (shift_env cutoff padding.length env))
                    (shift_env cutoff padding.length metaEnv)
                    { (shift_state cutoff padding s_inner) with heap := h'' })
                  = some (shift_val cutoff padding.length r,
                          shift_state cutoff padding s')
                -- shift_state cutoff padding s_inner has heap := shift_heap ... s_inner.heap.
                -- alloc on it appends shift_val v_e and returns idx = (shift_heap ...).length.
                -- shift_heap_length: (shift_heap _ _ s_inner.heap).length =
                --   s_inner.heap.length + padding.length.
                -- shift_idx s_inner.heap.length (since ≥ cutoff) = s_inner.heap.length + padding.length.
                simp only [shift_state, Heap.alloc]
                rw [shift_heap_length]
                -- Need: idx on B side = shift_idx cutoff padding.length s_inner.heap.length.
                have h_idx_eq :
                    s_inner.heap.length + padding.length =
                    shift_idx cutoff padding.length s_inner.heap.length := by
                  unfold shift_idx
                  rw [if_neg (by omega : ¬ s_inner.heap.length < cutoff)]
                -- Need to show the heap after alloc equals shift_heap (s_inner.heap ++ [v_e]).
                have h_heap_eq :
                    shift_heap cutoff padding s_inner.heap ++ [shift_val cutoff padding.length v_e] =
                    shift_heap cutoff padding (s_inner.heap ++ [v_e]) := by
                  rw [shift_heap_append cutoff padding s_inner.heap [v_e] h_cutoff_inner]
                  rfl
                rw [h_heap_eq]
                -- The alloc step gives us (heap ++ [v], heap.length).
                -- After rewriting, the body call should match h_body_b but with shifted env.
                -- env = (.cons x s_inner.heap.length env) → shift_env →
                --       (.cons x (shift_idx s_inner.heap.length) (shift_env env))
                -- shift_idx (since s_inner.heap.length ≥ cutoff) = s_inner.heap.length + padding.length.
                show eval k ptable body
                    (.cons x (s_inner.heap.length + padding.length)
                      (shift_env cutoff padding.length env))
                    (shift_env cutoff padding.length metaEnv)
                    (shift_state cutoff padding {s_inner with heap := s_inner.heap ++ [v_e]})
                  = some (shift_val cutoff padding.length r,
                          shift_state cutoff padding s')
                -- h_body_b should give us this if the env matches.
                -- shift_env (.cons x s_inner.heap.length env) =
                --   .cons x (shift_idx cutoff padding.length s_inner.heap.length) (shift_env cutoff padding.length env)
                --   = .cons x (s_inner.heap.length + padding.length) (shift_env env)  (by h_idx_eq)
                have h_env_eq :
                    shift_env cutoff padding.length (.cons x s_inner.heap.length env) =
                    .cons x (s_inner.heap.length + padding.length)
                      (shift_env cutoff padding.length env) := by
                  simp only [shift_env, ← h_idx_eq]
                rw [← h_env_eq]
                exact h_body_b
        | app exps =>
            cases exps with
            | nil =>
                simp only [eval] at h_eval
                exact absurd h_eval (by simp)
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable f env metaEnv s with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv, s1⟩ := pr
                    rw [hf] at h_eval
                    simp only at h_eval
                    have h_f_b := ih_eval ptable f env metaEnv s fv s1
                      hresp_pt hresp_init h_cutoff hf
                    have h_mono_f := (heap_mono k).1 ptable f env metaEnv s fv s1 hf
                    have h_cutoff_1 : cutoff ≤ s1.heap.length :=
                      Nat.le_trans h_cutoff h_mono_f
                    have h_pol_1 :=
                      pp_eval ptable f env metaEnv s fv s1 hresp_pt hresp_init hf
                    cases ha : evalList k ptable args env metaEnv s1 with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs, s2⟩ := pr2
                        rw [ha] at h_eval
                        simp only at h_eval
                        have h_a_b := ih_evalList ptable args env metaEnv s1 avs s2
                          hresp_pt h_pol_1 h_cutoff_1 ha
                        have h_mono_a :=
                          (heap_mono k).2.1 ptable args env metaEnv s1 avs s2 ha
                        have h_cutoff_2 : cutoff ≤ s2.heap.length :=
                          Nat.le_trans h_cutoff_1 h_mono_a
                        have h_pol_2 :=
                          pp_evalList ptable args env metaEnv s1 avs s2 hresp_pt h_pol_1 ha
                        have h_app_b := ih_applyVia ptable fv avs metaEnv s2 r s'
                          hresp_pt h_pol_2 h_cutoff_2 h_eval
                        simp [eval, h_f_b, h_a_b, h_app_b]
        | primApp f args =>
            simp only [eval] at h_eval
            cases hf : eval k ptable f env metaEnv s with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv, s1⟩ := pr
                rw [hf] at h_eval
                simp only at h_eval
                have h_f_b := ih_eval ptable f env metaEnv s fv s1
                  hresp_pt hresp_init h_cutoff hf
                have h_mono_f := (heap_mono k).1 ptable f env metaEnv s fv s1 hf
                have h_cutoff_1 : cutoff ≤ s1.heap.length :=
                  Nat.le_trans h_cutoff h_mono_f
                have h_pol_1 :=
                  pp_eval ptable f env metaEnv s fv s1 hresp_pt hresp_init hf
                cases ha : evalList k ptable args env metaEnv s1 with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs, s2⟩ := pr2
                    rw [ha] at h_eval
                    simp only at h_eval
                    have h_a_b := ih_evalList ptable args env metaEnv s1 avs s2
                      hresp_pt h_pol_1 h_cutoff_1 ha
                    have h_mono_a :=
                      (heap_mono k).2.1 ptable args env metaEnv s1 avs s2 ha
                    have h_cutoff_2 : cutoff ≤ s2.heap.length :=
                      Nat.le_trans h_cutoff_1 h_mono_a
                    have h_pol_2 :=
                      pp_evalList ptable args env metaEnv s1 avs s2 hresp_pt h_pol_1 ha
                    have h_app_b := ih_applyDirect ptable fv avs metaEnv s2 r s'
                      hresp_pt h_pol_2 h_cutoff_2 h_eval
                    simp [eval, h_f_b, h_a_b, h_app_b]
        | set x e =>
            -- The `.set` case requires `PolicyRespectsShift`-style invariance:
            -- the gate's verdict must agree on shifted vs unshifted inputs.
            -- We prove everything else here; the one remaining obligation is the
            -- policy-verdict equality (the inner `h_gate_eq` hypothesis below).
            -- The structure: handle bounds, isMetaMutation invariance, heap
            -- update commutativity. The proof is closed modulo a single
            -- `PolicyRespectsShift cutoff padding s.policy` assumption.
            simp only [eval] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s1⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e_b := ih_eval ptable e env metaEnv s v s1
                  hresp_pt hresp_init h_cutoff he
                have h_mono_e := (heap_mono k).1 ptable e env metaEnv s v s1 he
                have h_cutoff_1 : cutoff ≤ s1.heap.length :=
                  Nat.le_trans h_cutoff h_mono_e
                have h_pol_1 :=
                  pp_eval ptable e env metaEnv s v s1 hresp_pt hresp_init he
                cases hl : env.lookup x with
                | none => rw [hl] at h_eval; simp at h_eval
                | some idx =>
                    rw [hl] at h_eval
                    simp only at h_eval
                    -- isMetaMutation invariance under shift_env.
                    have h_meta_mut_eq : isMetaMutation x
                        (shift_env cutoff padding.length env)
                        (shift_env cutoff padding.length metaEnv)
                      = isMetaMutation x env metaEnv := by
                      unfold isMetaMutation
                      cases hxe : env.lookup x with
                      | none =>
                          rw [shift_env_lookup_none cutoff padding.length env x hxe]
                      | some i_e =>
                          rw [shift_env_lookup cutoff padding.length env x i_e hxe]
                          cases hxm : metaEnv.lookup x with
                          | none =>
                              rw [shift_env_lookup_none cutoff padding.length metaEnv x hxm]
                          | some i_m =>
                              rw [shift_env_lookup cutoff padding.length metaEnv x i_m hxm]
                              -- shift_idx i_e == shift_idx i_m ↔ i_e == i_m.
                              show (shift_idx cutoff padding.length i_e ==
                                    shift_idx cutoff padding.length i_m)
                                  = (i_e == i_m)
                              by_cases hi : i_e = i_m
                              · subst hi; simp
                              · have h_neq :
                                    shift_idx cutoff padding.length i_e
                                    ≠ shift_idx cutoff padding.length i_m := by
                                  intro h_eq
                                  unfold shift_idx at h_eq
                                  by_cases h1 : i_e < cutoff
                                  · rw [if_pos h1] at h_eq
                                    by_cases h2 : i_m < cutoff
                                    · rw [if_pos h2] at h_eq; exact hi h_eq
                                    · rw [if_neg h2] at h_eq; omega
                                  · rw [if_neg h1] at h_eq
                                    by_cases h2 : i_m < cutoff
                                    · rw [if_pos h2] at h_eq; omega
                                    · rw [if_neg h2] at h_eq
                                      have : i_e = i_m := by omega
                                      exact hi this
                                have h1 :
                                    (shift_idx cutoff padding.length i_e ==
                                     shift_idx cutoff padding.length i_m) = false := by
                                  simp [h_neq]
                                have h2 : (i_e == i_m) = false := by simp [hi]
                                rw [h1, h2]
                    -- env.lookup x = some idx → idx is whatever was bound.
                    -- For .set we don't have direct EnvValid; idx may be ≥ s1.heap.length.
                    -- The general shift_heap_update handles both cases.
                    -- Prepare shift goal expansion.
                    have h_state_heap :
                        (shift_state cutoff padding s).heap = shift_heap cutoff padding s.heap := rfl
                    show eval (k+1) ptable (.set x e) _ _ _ = _
                    simp only [eval, h_e_b,
                      shift_env_lookup cutoff padding.length env x idx hl,
                      h_meta_mut_eq, ↓reduceIte]
                    split at h_eval
                    · -- isMetaMutation = true.
                      rename_i h_meta_mut
                      simp only [h_meta_mut, if_true]
                      cases hp : s1.heap[idx]? with
                      | none => rw [hp] at h_eval; simp at h_eval
                      | some oldVal =>
                          rw [hp] at h_eval
                          simp only at h_eval
                          -- Lookup at shift_idx idx gives shift_val oldVal.
                          have h_shift_state_heap :
                              (shift_state cutoff padding s1).heap
                                = shift_heap cutoff padding s1.heap := rfl
                          rw [h_shift_state_heap,
                              shift_heap_getElem? cutoff padding s1.heap idx h_cutoff_1, hp]
                          simp only [Option.map_some]
                          -- Gate verdict equality (discharged from `PolicyRespectsShift`).
                          -- Side A: s.policy { ..., heap := s1.heap, env := env, metaEnv := metaEnv, index := idx} oldVal v
                          -- Side B: s.policy { ..., heap := shift_heap s1.heap, env := shift_env env,
                          --                    metaEnv := shift_env metaEnv, index := shift_idx idx}
                          --                  (shift_val oldVal) (shift_val v)
                          -- These are equal by `PolicyRespectsShift cutoff padding s.policy`.
                          have h_gate_eq :
                              s.policy
                                { target := x, heap := shift_heap cutoff padding s1.heap,
                                  env := shift_env cutoff padding.length env,
                                  metaEnv := shift_env cutoff padding.length metaEnv,
                                  index := shift_idx cutoff padding.length idx }
                                (shift_val cutoff padding.length oldVal)
                                (shift_val cutoff padding.length v)
                              = s.policy
                                { target := x, heap := s1.heap, env := env,
                                  metaEnv := metaEnv, index := idx }
                                oldVal v := by
                            -- This is exactly the contrapositive direction of
                            -- `PolicyRespectsShift cutoff padding s.policy` applied at the
                            -- relevant arguments.
                            exact (hresp_init x idx env metaEnv s1.heap oldVal v h_cutoff_1).symm
                          -- gate's value on side A.
                          split at h_eval
                          · -- gate accepted on A.
                            rename_i h_admit_a
                            simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨h_r, h_s⟩ := h_eval
                            subst h_r; subst h_s
                            -- On B, the gate also accepts (by h_gate_eq).
                            have h_admit_b :
                                s.policy
                                  { target := x, heap := shift_heap cutoff padding s1.heap,
                                    env := shift_env cutoff padding.length env,
                                    metaEnv := shift_env cutoff padding.length metaEnv,
                                    index := shift_idx cutoff padding.length idx }
                                  (shift_val cutoff padding.length oldVal)
                                  (shift_val cutoff padding.length v) = true := by
                              rw [h_gate_eq]; exact h_admit_a
                            -- shift_state s.policy = s.policy (by definition of shift_state).
                            have h_state_pol : (shift_state cutoff padding s).policy = s.policy := rfl
                            rw [h_state_pol]
                            simp only [h_admit_b, shift_val, if_true, ↓reduceIte]
                            -- Update commutativity.
                            simp only [shift_state]
                            rw [shift_heap_update_general cutoff padding s1.heap idx v h_cutoff_1]
                          · -- gate rejected on A.
                            rename_i h_reject_a
                            simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                            obtain ⟨h_r, h_s⟩ := h_eval
                            subst h_r; subst h_s
                            -- h_reject_a: gate verdict on A = false (the if's else branch).
                            have h_reject_b :
                                s.policy
                                  { target := x, heap := shift_heap cutoff padding s1.heap,
                                    env := shift_env cutoff padding.length env,
                                    metaEnv := shift_env cutoff padding.length metaEnv,
                                    index := shift_idx cutoff padding.length idx }
                                  (shift_val cutoff padding.length oldVal)
                                  (shift_val cutoff padding.length v) = false := by
                              rw [h_gate_eq]
                              -- h_reject_a is the negation of `... = true`, which on Bool means `= false`.
                              cases h_b : s.policy { target := x, heap := s1.heap, env := env,
                                                      metaEnv := metaEnv, index := idx } oldVal v with
                              | true => exact absurd h_b h_reject_a
                              | false => rfl
                            have h_state_pol : (shift_state cutoff padding s).policy = s.policy := rfl
                            rw [h_state_pol]
                            rw [h_reject_b]
                            simp [shift_val]
                    · -- isMetaMutation = false: plain mutation.
                      rename_i h_not_meta
                      have h_not_meta_eq : isMetaMutation x env metaEnv = false := by
                        cases h_b : isMetaMutation x env metaEnv with
                        | true => exact absurd h_b h_not_meta
                        | false => rfl
                      simp only [h_not_meta_eq, Bool.false_eq_true, ↓reduceIte]
                      simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                      obtain ⟨h_r, h_s⟩ := h_eval
                      subst h_r; subst h_s
                      simp only [shift_val, shift_state]
                      rw [shift_heap_update_general cutoff padding s1.heap idx v h_cutoff_1]
      · -- evalList (k+1)
        intro ptable exps env metaEnv s rs s' hresp_pt hresp_init h_cutoff h_eval
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_s⟩ := h_eval
            subst h_r; subst h_s
            simp [evalList, shift_listVal]
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable e env metaEnv s with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, s_inner⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                have h_e_b := ih_eval ptable e env metaEnv s v s_inner
                  hresp_pt hresp_init h_cutoff he
                have h_mono_e := (heap_mono k).1 ptable e env metaEnv s v s_inner he
                have h_cutoff_inner : cutoff ≤ s_inner.heap.length :=
                  Nat.le_trans h_cutoff h_mono_e
                have h_pol_inner :=
                  pp_eval ptable e env metaEnv s v s_inner hresp_pt hresp_init he
                cases hr : evalList k ptable rest env metaEnv s_inner with
                | none => rw [hr] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨vs, s2⟩ := pr2
                    rw [hr] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_rs, h_s⟩ := h_eval
                    subst h_rs; subst h_s
                    have h_r_b :=
                      ih_evalList ptable rest env metaEnv s_inner vs s2
                        hresp_pt h_pol_inner h_cutoff_inner hr
                    simp [evalList, h_e_b, h_r_b, shift_listVal]
      · -- applyVia (k+1)
        intro ptable op args metaEnv s r s' hresp_pt hresp_init h_cutoff h_app
        simp only [applyVia] at h_app
        cases hl : metaEnv.lookup "base-apply" with
        | none =>
            rw [hl] at h_app
            have h_app_b :=
              ih_applyDirect ptable op args metaEnv s r s'
                hresp_pt hresp_init h_cutoff h_app
            show applyVia (k+1) ptable _ _ _ _ = _
            simp only [applyVia,
              shift_env_lookup_none cutoff padding.length metaEnv "base-apply" hl]
            exact h_app_b
        | some idx =>
            rw [hl] at h_app
            simp only at h_app
            cases hp : s.heap[idx]? with
            | none => rw [hp] at h_app; simp at h_app
            | some baseApply =>
                rw [hp] at h_app
                cases baseApply with
                | builtinBaseApply =>
                    simp only at h_app
                    have h_app_b :=
                      ih_applyDirect ptable op args metaEnv s r s'
                        hresp_pt hresp_init h_cutoff h_app
                    show applyVia (k+1) ptable _ _ _ _ = _
                    have h_state_heap :
                        (shift_state cutoff padding s).heap = shift_heap cutoff padding s.heap := rfl
                    simp only [applyVia,
                      shift_env_lookup cutoff padding.length metaEnv "base-apply" idx hl,
                      h_state_heap,
                      shift_heap_getElem? cutoff padding s.heap idx h_cutoff,
                      hp, Option.map_some, shift_val]
                    exact h_app_b
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
                    simp only at h_app
                    have h_app_b :=
                      ih_applyDirect ptable _ [op, listToVal args] metaEnv s r s'
                        hresp_pt hresp_init h_cutoff h_app
                    show applyVia (k+1) ptable _ _ _ _ = _
                    have h_state_heap :
                        (shift_state cutoff padding s).heap = shift_heap cutoff padding s.heap := rfl
                    simp only [applyVia,
                      shift_env_lookup cutoff padding.length metaEnv "base-apply" idx hl,
                      h_state_heap,
                      shift_heap_getElem? cutoff padding s.heap idx h_cutoff,
                      hp, Option.map_some, shift_val]
                    rw [show shift_listVal cutoff padding.length [op, listToVal args]
                          = [shift_val cutoff padding.length op,
                             shift_val cutoff padding.length (listToVal args)] from rfl] at h_app_b
                    rw [shift_val_listToVal cutoff padding.length args] at h_app_b
                    exact h_app_b
      · -- applyDirect (k+1)
        intro ptable op args metaEnv s r s' hresp_pt hresp_init h_cutoff h_app
        simp only [applyDirect] at h_app
        cases op with
        | num _ => exact absurd h_app (by simp)
        | bool _ => exact absurd h_app (by simp)
        | nilV => exact absurd h_app (by simp)
        | sym _ => exact absurd h_app (by simp)
        | cons _ _ => exact absurd h_app (by simp)
        | prim name =>
            simp only at h_app
            cases hp : applyPrim name args with
            | none => rw [hp] at h_app; simp at h_app
            | some v =>
                rw [hp] at h_app
                simp only [Option.some.injEq, Prod.mk.injEq] at h_app
                obtain ⟨h_r, h_s⟩ := h_app
                subst h_r; subst h_s
                show applyDirect (k+1) ptable _ _ _ _ = _
                simp only [applyDirect, shift_val]
                rw [shift_applyPrim cutoff padding.length name args, hp]
                rfl
        | builtinBaseApply =>
            simp only at h_app
            cases args with
            | nil => simp at h_app
            | cons a as =>
                cases as with
                | nil => simp at h_app
                | cons o rest =>
                    cases rest with
                    | nil =>
                        simp only at h_app
                        cases hv : valToList o with
                        | none => rw [hv] at h_app; simp at h_app
                        | some operands =>
                            rw [hv] at h_app
                            -- operands valid in s.heap; cutoff ≤ s.heap.length still holds.
                            have h_app_b :=
                              ih_applyDirect ptable a operands metaEnv s r s'
                                hresp_pt hresp_init h_cutoff h_app
                            show applyDirect (k+1) ptable _ _ _ _ = _
                            simp only [applyDirect, shift_listVal, shift_val]
                            rw [shift_listVal_valToList cutoff padding.length o, hv]
                            simp only [Option.map_some]
                            exact h_app_b
                    | cons _ _ => simp at h_app
        | closure ps body cenv =>
            simp only at h_app
            split at h_app
            · simp at h_app
            · rename_i h_len_neq
              -- h_len_neq : ¬(ps.length != args.length) = true
              have h_len_eq : ps.length = args.length := by
                have h := h_len_neq
                simp at h
                exact h
              have h_foldl_len :
                  ((args.zip ps).foldl allocStep (s.heap, cenv)).1.length
                    = s.heap.length + (args.zip ps).length :=
                allocStep_foldl_length (args.zip ps) s.heap cenv
              have h_cutoff_alloc :
                  cutoff ≤ ((args.zip ps).foldl allocStep (s.heap, cenv)).1.length := by
                rw [h_foldl_len]; omega
              -- Policy of {s with heap := ...} is the same as s.
              have h_pol_alloc :
                  PolicyRespectsShift cutoff padding
                    ({s with heap := ((args.zip ps).foldl allocStep (s.heap, cenv)).1} : RunState).policy :=
                hresp_init
              have h_body_b := ih_eval ptable body
                ((args.zip ps).foldl allocStep (s.heap, cenv)).2 metaEnv
                {s with heap := ((args.zip ps).foldl allocStep (s.heap, cenv)).1} r s'
                hresp_pt h_pol_alloc h_cutoff_alloc h_app
              have h_zip_eq :
                  (shift_listVal cutoff padding.length args).zip ps
                    = (args.zip ps).map (fun vp => (shift_val cutoff padding.length vp.1, vp.2)) := by
                rw [shift_listVal_eq_map]
                clear h_foldl_len h_cutoff_alloc h_body_b h_app h_len_neq h_len_eq h_pol_alloc
                induction args generalizing ps with
                | nil => simp
                | cons a as ih =>
                    cases ps with
                    | nil => simp
                    | cons p ps' =>
                        simp only [List.zip_cons_cons, List.map_cons]
                        rw [ih ps']
              have h_shift := allocStep_foldl_shift cutoff padding
                (args.zip ps) s.heap cenv h_cutoff
              simp only at h_shift
              obtain ⟨h_fst, h_snd⟩ := h_shift
              show applyDirect (k+1) ptable
                (shift_val cutoff padding.length (.closure ps body cenv))
                (shift_listVal cutoff padding.length args)
                (shift_env cutoff padding.length metaEnv)
                (shift_state cutoff padding s)
                = some (shift_val cutoff padding.length r, shift_state cutoff padding s')
              simp only [shift_val, applyDirect]
              have h_len_b :
                  (ps.length != (shift_listVal cutoff padding.length args).length) = false := by
                rw [shift_listVal_length]
                simp [h_len_eq]
              simp only [h_len_b, Bool.false_eq_true, ↓reduceIte]
              rw [h_zip_eq]
              simp only [shift_state]
              -- Convert the inline lambda in the goal to `allocStep` so h_fst/h_snd apply.
              show eval k ptable body
                  ((List.map (fun vp => (shift_val cutoff padding.length vp.1, vp.2))
                      (args.zip ps)).foldl
                    allocStep (shift_heap cutoff padding s.heap,
                              shift_env cutoff padding.length cenv)).2
                  (shift_env cutoff padding.length metaEnv)
                  { heap := ((List.map (fun vp => (shift_val cutoff padding.length vp.1, vp.2))
                              (args.zip ps)).foldl
                              allocStep (shift_heap cutoff padding s.heap,
                                        shift_env cutoff padding.length cenv)).1,
                    policy := s.policy }
                = some (shift_val cutoff padding.length r,
                        { heap := shift_heap cutoff padding s'.heap, policy := s'.policy })
              rw [h_fst, h_snd]
              exact h_body_b

/-- Helper: a value retrieved from a `ListValValid` list is `ValValid`. -/
private theorem ListValValid.getElem_valid : ∀ {xs : List Val} {h : Heap},
    ListValValid xs h →
    ∀ (i : Nat) (v : Val), xs[i]? = some v → ValValid v h
  | [],      _, _,  i, v, hi => by simp at hi
  | x :: xs, _, hv, i, v, hi => by
      obtain ⟨hv_h, hv_t⟩ := hv
      cases i with
      | zero => simp at hi; exact hi ▸ hv_h
      | succ k => simp at hi; exact ListValValid.getElem_valid hv_t k v hi

/-- **Shift-based prefix extension.** Same conclusion as
    `applyDirect_heap_extend_weak`, but proved via the sorry-free
    `shift_respect` infrastructure. Stronger preconditions: deep
    validity of `op`/`operands`/`metaEnv`/`s.heap`, plus the policies
    `ptable`/`s.policy` are `PolicyRespectsShift` at the relevant
    cutoff/padding.

    Uses `shift_respect` to obtain the shifted-side computation,
    `shift_heap_id_of_deep` to identify the shifted state with the
    prefix-extended state, and `valVis_weak_self_shift` to bridge
    the result `r` to its shift. -/
theorem applyDirect_heap_extend_via_shift
    {fuel : Nat} {ptable : PolicyTable} {op : Val} {operands : List Val}
    {metaEnv : Env} {s : RunState}
    (hresp_pt_b : PolicyTableRespectsBisim ptable)
    (h_heap : HeapValid s.heap) (h_op : ValValid op s.heap)
    (h_operands : ListValValid operands s.heap)
    (h_meta : EnvValid metaEnv s.heap)
    (hresp_init_b : PolicyRespectsBisim s.policy)
    (extras : List Val) (h_extras : ListValValid extras s.heap)
    (h_heap_deep : HeapDeep s.heap) (h_op_deep : ValDeep op s.heap)
    (h_operands_deep : ListValDeep operands s.heap)
    (h_meta_deep : EnvDeep metaEnv s.heap)
    (hresp_pt : PolicyTableRespectsShift s.heap.length extras ptable)
    (hresp_init : PolicyRespectsShift s.heap.length extras s.policy)
    {r : Val} {s' : RunState}
    (h_app : applyDirect fuel ptable op operands metaEnv s = some (r, s')) :
    ∃ r' s'',
      applyDirect fuel ptable op operands metaEnv
        { heap := s.heap ++ extras, policy := s.policy } = some (r', s'') ∧
      ValVis_weak r r' s'.heap s''.heap ∧
      HeapValid s''.heap ∧
      s'.policy = s''.policy ∧
      s.heap.length + extras.length ≤ s''.heap.length := by
  -- Apply shift_respect at cutoff = s.heap.length, padding = extras.
  obtain ⟨_, _, _, ih_apd⟩ := shift_respect s.heap.length extras fuel
  have h_cutoff : s.heap.length ≤ s.heap.length := Nat.le_refl _
  have h_app_shifted := ih_apd ptable op operands metaEnv s r s'
    hresp_pt hresp_init h_cutoff h_app
  -- Convert shifted forms back to identity using deep validity.
  have h_op_below : Val.AllBelow s.heap.length op := ValDeep.toAllBelow h_op_deep
  have h_operands_below : ListVal.AllBelow s.heap.length operands :=
    ListValDeep.toAllBelow h_operands_deep
  have h_meta_below : Env.AllBelow s.heap.length metaEnv :=
    EnvDeep.toAllBelow h_meta_deep
  rw [shift_val_id s.heap.length extras.length h_op_below,
      shift_listVal_id s.heap.length extras.length h_operands_below,
      shift_env_id s.heap.length extras.length h_meta_below] at h_app_shifted
  -- Convert shift_state s to {heap := s.heap ++ extras, policy := s.policy}.
  have h_state_eq :
      shift_state s.heap.length extras s = { heap := s.heap ++ extras, policy := s.policy } := by
    simp only [shift_state]
    rw [shift_heap_id_of_deep extras s.heap h_heap_deep]
  rw [h_state_eq] at h_app_shifted
  -- Now h_app_shifted gives us applyDirect on the prefix-extended state.
  refine ⟨shift_val s.heap.length extras.length r,
          shift_state s.heap.length extras s', h_app_shifted, ?_, ?_, ?_, ?_⟩
  · -- ValVis_weak r (shift_val r) s'.heap (shift_state s').heap.
    -- Need: HeapValid s'.heap and ValValid r s'.heap.
    -- Get from applyDirect_preserves_validity (frame-derived).
    obtain ⟨h_heap', hv_r, _, _⟩ :=
      applyDirect_preserves_validity hresp_pt_b h_heap h_op h_operands h_meta
        hresp_init_b h_app
    have h_mono : s.heap.length ≤ s'.heap.length :=
      (heap_mono fuel).2.2.2 ptable op operands metaEnv s r s' h_app
    -- (shift_state s').heap = shift_heap s.heap.length extras s'.heap.
    show ValVis_weak r (shift_val s.heap.length extras.length r)
      s'.heap (shift_state s.heap.length extras s').heap
    have h_state_heap_eq :
        (shift_state s.heap.length extras s').heap
          = shift_heap s.heap.length extras s'.heap := rfl
    rw [h_state_heap_eq]
    exact valVis_weak_self_shift s.heap.length extras s'.heap h_heap' h_mono r hv_r
  · -- HeapValid (shift_state s').heap.
    -- Apply applyDirect_preserves_validity to the prefix-extended call.
    have hext : ∃ ex, s.heap ++ extras = s.heap ++ ex := ⟨extras, rfl⟩
    have h_heap_b : HeapValid (s.heap ++ extras) := by
      intro i v hi
      by_cases h_lt : i < s.heap.length
      · have h_eq : (s.heap ++ extras)[i]? = s.heap[i]? :=
          getElem?_prefix s.heap extras i h_lt
        rw [h_eq] at hi
        exact ValValid.heap_extends v (h_heap i v hi) hext
      · have h_le : s.heap.length ≤ i := Nat.le_of_not_lt h_lt
        have h_eq : (s.heap ++ extras)[i]? = extras[i - s.heap.length]? :=
          List.getElem?_append_right h_le
        rw [h_eq] at hi
        exact ValValid.heap_extends v
          (ListValValid.getElem_valid h_extras (i - s.heap.length) v hi) hext
    have h_op_b : ValValid op (s.heap ++ extras) := ValValid.heap_extends op h_op hext
    have h_operands_b : ListValValid operands (s.heap ++ extras) :=
      ListValValid.heap_extends h_operands hext
    have h_meta_b : EnvValid metaEnv (s.heap ++ extras) :=
      EnvValid.heap_extends h_meta hext
    obtain ⟨h_heap_out, _, _, _⟩ :=
      @applyDirect_preserves_validity fuel ptable hresp_pt_b op operands metaEnv
        { heap := s.heap ++ extras, policy := s.policy }
        h_heap_b h_op_b h_operands_b h_meta_b hresp_init_b _ _ h_app_shifted
    -- h_heap_out : HeapValid (...).heap where ... is the output state.
    -- The output state from h_app_shifted is shift_state s.heap.length extras s'.
    exact h_heap_out
  · -- s'.policy = (shift_state s').policy.
    show s'.policy = (shift_state s.heap.length extras s').policy
    simp [shift_state]
  · -- s.heap.length + extras.length ≤ (shift_state s').heap.length.
    show s.heap.length + extras.length ≤ (shift_state s.heap.length extras s').heap.length
    have : (shift_state s.heap.length extras s').heap.length
        = s'.heap.length + extras.length := by
      simp [shift_state, shift_heap_length]
    rw [this]
    have h_mono : s.heap.length ≤ s'.heap.length :=
      (heap_mono fuel).2.2.2 ptable op operands metaEnv s r s' h_app
    omega

/-- **Prefix-extension lemma** — proved via `shift_respect`
    (specifically `applyDirect_heap_extend_via_shift`). Takes
    Deep-validity (`HeapDeep`/`ValDeep`/`ListValDeep`/`EnvDeep`) and
    `PolicyRespectsShift` hypotheses as additional preconditions;
    callers discharge them. For the runner's startup state these
    are all proven: `runtime_invariants_initial` gives Deep
    validity, `verifiedTable_respects_shift` and
    `acceptAllPolicy_respects_shift` give the policy hypotheses. -/
theorem applyDirect_heap_extend_weak
    {fuel : Nat} {ptable : PolicyTable} {op : Val} {operands : List Val}
    {metaEnv : Env} {s : RunState}
    (hresp_pt : PolicyTableRespectsBisim ptable)
    (h_heap : HeapValid s.heap) (h_op : ValValid op s.heap)
    (h_operands : ListValValid operands s.heap)
    (h_meta : EnvValid metaEnv s.heap)
    (hresp_init : PolicyRespectsBisim s.policy)
    {r : Val} {s' : RunState}
    (h_app : applyDirect fuel ptable op operands metaEnv s = some (r, s'))
    (extras : List Val) (h_extras : ListValValid extras s.heap)
    (h_heap_deep : HeapDeep s.heap) (h_op_deep : ValDeep op s.heap)
    (h_operands_deep : ListValDeep operands s.heap)
    (h_meta_deep : EnvDeep metaEnv s.heap)
    (h_pt_shift : PolicyTableRespectsShift s.heap.length extras ptable)
    (h_pol_shift : PolicyRespectsShift s.heap.length extras s.policy) :
    ∃ r' s'',
      applyDirect fuel ptable op operands metaEnv
        { heap := s.heap ++ extras, policy := s.policy } = some (r', s'') ∧
      ValVis_weak r r' s'.heap s''.heap ∧
      HeapValid s''.heap ∧
      s'.policy = s''.policy ∧
      s.heap.length + extras.length ≤ s''.heap.length :=
  applyDirect_heap_extend_via_shift hresp_pt h_heap h_op h_operands h_meta
    hresp_init extras h_extras h_heap_deep h_op_deep h_operands_deep h_meta_deep
    h_pt_shift h_pol_shift h_app

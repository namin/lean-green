/-
  lean-black: a Black-faithful reflective interpreter in Lean 4.

  Substrate. Defines the core types and the four-way mutual eval
  block. Policy infrastructure (the library of `BlackPolicy`s and
  their soundness theorems) lives in `LeanBlack/Policies.lean`;
  the value/env bisimulation infrastructure lives in
  `LeanBlack/Bisim.lean`; the LLM cascade is in `Bedrock.lean` /
  `Elab.lean` / `Runner.lean`.

  Three architectural commitments live in this file:

  1. **Causal connection.** `base-apply` is a value in the meta-env,
     not a fixed Lean function. Every Black-level application
     dispatches through `metaEnv.lookup "base-apply" >>= heap[·]?`.
     Mutating that heap cell observably changes future dispatch.

  2. **Heap-cell bindings.** `Env := List (String × Nat)` where the
     `Nat` indexes a `Heap := List Val`. Closures capture envs by
     index, so mutations to a cell propagate to every closure that
     looked it up.

  3. **Policy-gated meta-mutations.** `set!` consults the current
     `BlackPolicy` (a value in `RunState`) iff the target heap cell
     is bound in the meta-env (detected by `isMetaMutation`). Plain
     mutations are not gated.

  Stage-1 simplifications (these are scoping decisions, not
  mistakes in design):

  - Fuel-based functional big-step semantics. Standard CakeML
    pattern (Kumar 2016 §3.4). Divergence is "out of fuel".
  - Only `base-apply` is reified in the meta-env. Reifying
    `base-eval`, `eval-if`, etc. is a future extension; the
    architecture supports it without redesign.
  - One meta-env, not a per-level tower. `(em (em body))` reuses
    the same meta-env in this stage.
-/

mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | nilV    : Val
  | cons    : Val → Val → Val
  | sym     : String → Val
  | closure : List String → Expr → Env → Val
  | prim    : String → Val
  | builtinBaseApply : Val
  deriving Repr

inductive Expr where
  | num           : Int → Expr
  | bool          : Bool → Expr
  | quote         : Val → Expr
  | var           : String → Expr
  | ifte          : Expr → Expr → Expr → Expr
  | lam           : List String → Expr → Expr
  | app           : List Expr → Expr
  | set           : String → Expr → Expr
  | em            : Expr → Expr
  | primApp       : Expr → List Expr → Expr
  | letE          : String → Expr → Expr → Expr
  | seq           : List Expr → Expr
  | installPolicy : Nat → Expr
  deriving Repr

inductive Env where
  | nil  : Env
  | cons : String → Nat → Env → Env
  deriving Repr
end

mutual
  /-- Boolean equality on `Val`. Mutually recursive with `exprBeq`
      and `envBeq` because `Val.closure` carries an `Expr` body and
      an `Env` cenv. Used by ctx-aware policies that compare a
      proposed value to a heap cell (multi-install soundness). -/
  def Val.beq : Val → Val → Bool
    | .num a,             .num b             => a == b
    | .bool a,            .bool b             => a == b
    | .nilV,              .nilV               => true
    | .cons x₁ y₁,        .cons x₂ y₂         => Val.beq x₁ x₂ && Val.beq y₁ y₂
    | .sym a,             .sym b              => a == b
    | .closure ps₁ b₁ e₁, .closure ps₂ b₂ e₂  =>
        ps₁ == ps₂ && Expr.beq b₁ b₂ && Env.beq e₁ e₂
    | .prim a,            .prim b             => a == b
    | .builtinBaseApply,  .builtinBaseApply   => true
    | _,                  _                   => false

  def Expr.beq : Expr → Expr → Bool
    | .num a,         .num b         => a == b
    | .bool a,        .bool b         => a == b
    | .quote a,       .quote b        => Val.beq a b
    | .var a,         .var b          => a == b
    | .ifte c₁ t₁ e₁, .ifte c₂ t₂ e₂  =>
        Expr.beq c₁ c₂ && Expr.beq t₁ t₂ && Expr.beq e₁ e₂
    | .lam ps₁ b₁,    .lam ps₂ b₂    => ps₁ == ps₂ && Expr.beq b₁ b₂
    | .app es₁,       .app es₂        => exprListBeq es₁ es₂
    | .set x₁ e₁,     .set x₂ e₂      => x₁ == x₂ && Expr.beq e₁ e₂
    | .em b₁,         .em b₂          => Expr.beq b₁ b₂
    | .primApp f₁ as₁, .primApp f₂ as₂ =>
        Expr.beq f₁ f₂ && exprListBeq as₁ as₂
    | .letE x₁ e₁ b₁, .letE x₂ e₂ b₂  =>
        x₁ == x₂ && Expr.beq e₁ e₂ && Expr.beq b₁ b₂
    | .seq es₁,       .seq es₂        => exprListBeq es₁ es₂
    | .installPolicy a, .installPolicy b => a == b
    | _,              _                => false

  def exprListBeq : List Expr → List Expr → Bool
    | [],      []      => true
    | x :: xs, y :: ys => Expr.beq x y && exprListBeq xs ys
    | _,       _        => false

  def Env.beq : Env → Env → Bool
    | .nil,           .nil           => true
    | .cons k₁ i₁ r₁, .cons k₂ i₂ r₂ => k₁ == k₂ && i₁ == i₂ && Env.beq r₁ r₂
    | _,              _               => false
end

/-- `==` for `Val` (used by the policy gate). -/
instance : BEq Val := ⟨Val.beq⟩

/-! ## Correctness of structural beq

    Mutual induction proving each `_.beq a b = true → a = b`. The
    runtime policy uses `Val.beq` to compare a heap cell to an
    expected value (multi-install: captured `orig` ≡ current
    `base-apply`); this lemma lifts the Bool admission into a
    propositional equality the bridge lemma can use. -/

mutual

theorem val_beq_eq : ∀ (a b : Val), Val.beq a b = true → a = b
  | .num x,             .num y,            h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .bool x,            .bool y,           h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .nilV,              .nilV,             _ => rfl
  | .sym x,             .sym y,            h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .prim x,            .prim y,           h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .builtinBaseApply,  .builtinBaseApply, _ => rfl
  | .cons x₁ y₁,        .cons x₂ y₂,       h => by
      simp only [Val.beq, Bool.and_eq_true] at h
      exact (val_beq_eq x₁ x₂ h.1) ▸ (val_beq_eq y₁ y₂ h.2) ▸ rfl
  | .closure ps₁ b₁ e₁, .closure ps₂ b₂ e₂, h => by
      simp only [Val.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ (expr_beq_eq b₁ b₂ h.1.2) ▸
            (env_beq_eq e₁ e₂ h.2) ▸ rfl
  -- All mismatched-constructor cases follow uniformly: Val.beq
  -- returns false on mismatch, contradicting h.
  | .num _, .bool _, h | .num _, .nilV, h | .num _, .cons _ _, h
  | .num _, .sym _, h | .num _, .closure _ _ _, h | .num _, .prim _, h
  | .num _, .builtinBaseApply, h
  | .bool _, .num _, h | .bool _, .nilV, h | .bool _, .cons _ _, h
  | .bool _, .sym _, h | .bool _, .closure _ _ _, h | .bool _, .prim _, h
  | .bool _, .builtinBaseApply, h
  | .nilV, .num _, h | .nilV, .bool _, h | .nilV, .cons _ _, h
  | .nilV, .sym _, h | .nilV, .closure _ _ _, h | .nilV, .prim _, h
  | .nilV, .builtinBaseApply, h
  | .cons _ _, .num _, h | .cons _ _, .bool _, h | .cons _ _, .nilV, h
  | .cons _ _, .sym _, h | .cons _ _, .closure _ _ _, h
  | .cons _ _, .prim _, h | .cons _ _, .builtinBaseApply, h
  | .sym _, .num _, h | .sym _, .bool _, h | .sym _, .nilV, h
  | .sym _, .cons _ _, h | .sym _, .closure _ _ _, h
  | .sym _, .prim _, h | .sym _, .builtinBaseApply, h
  | .closure _ _ _, .num _, h | .closure _ _ _, .bool _, h
  | .closure _ _ _, .nilV, h | .closure _ _ _, .cons _ _, h
  | .closure _ _ _, .sym _, h | .closure _ _ _, .prim _, h
  | .closure _ _ _, .builtinBaseApply, h
  | .prim _, .num _, h | .prim _, .bool _, h | .prim _, .nilV, h
  | .prim _, .cons _ _, h | .prim _, .sym _, h
  | .prim _, .closure _ _ _, h | .prim _, .builtinBaseApply, h
  | .builtinBaseApply, .num _, h | .builtinBaseApply, .bool _, h
  | .builtinBaseApply, .nilV, h | .builtinBaseApply, .cons _ _, h
  | .builtinBaseApply, .sym _, h | .builtinBaseApply, .closure _ _ _, h
  | .builtinBaseApply, .prim _, h => by simp [Val.beq] at h

theorem expr_beq_eq : ∀ (a b : Expr), Expr.beq a b = true → a = b
  | .num x,            .num y,            h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .bool x,           .bool y,           h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .quote x,          .quote y,          h => by
      simp only [Expr.beq] at h; exact (val_beq_eq x y h) ▸ rfl
  | .var x,            .var y,            h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .ifte c₁ t₁ e₁,    .ifte c₂ t₂ e₂,    h => by
      simp only [Expr.beq, Bool.and_eq_true] at h
      exact (expr_beq_eq c₁ c₂ h.1.1) ▸ (expr_beq_eq t₁ t₂ h.1.2) ▸
            (expr_beq_eq e₁ e₂ h.2) ▸ rfl
  | .lam ps₁ b₁,       .lam ps₂ b₂,       h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1 ▸ (expr_beq_eq b₁ b₂ h.2) ▸ rfl
  | .app es₁,          .app es₂,          h => by
      simp only [Expr.beq] at h; exact (expr_list_beq_eq es₁ es₂ h) ▸ rfl
  | .set x₁ e₁,        .set x₂ e₂,        h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1 ▸ (expr_beq_eq e₁ e₂ h.2) ▸ rfl
  | .em b₁,            .em b₂,            h => by
      simp only [Expr.beq] at h; exact (expr_beq_eq b₁ b₂ h) ▸ rfl
  | .primApp f₁ as₁,   .primApp f₂ as₂,   h => by
      simp only [Expr.beq, Bool.and_eq_true] at h
      exact (expr_beq_eq f₁ f₂ h.1) ▸ (expr_list_beq_eq as₁ as₂ h.2) ▸ rfl
  | .letE x₁ e₁ b₁,    .letE x₂ e₂ b₂,    h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ (expr_beq_eq e₁ e₂ h.1.2) ▸ (expr_beq_eq b₁ b₂ h.2) ▸ rfl
  | .seq es₁,          .seq es₂,          h => by
      simp only [Expr.beq] at h; exact (expr_list_beq_eq es₁ es₂ h) ▸ rfl
  | .installPolicy x,  .installPolicy y,  h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  -- Mismatched constructors. Each combination unfolds to false = true
  -- via simp on Expr.beq.
  | .num _, .bool _, h | .num _, .quote _, h | .num _, .var _, h
  | .num _, .ifte _ _ _, h | .num _, .lam _ _, h | .num _, .app _, h
  | .num _, .set _ _, h | .num _, .em _, h | .num _, .primApp _ _, h
  | .num _, .letE _ _ _, h | .num _, .seq _, h | .num _, .installPolicy _, h
  | .bool _, .num _, h | .bool _, .quote _, h | .bool _, .var _, h
  | .bool _, .ifte _ _ _, h | .bool _, .lam _ _, h | .bool _, .app _, h
  | .bool _, .set _ _, h | .bool _, .em _, h | .bool _, .primApp _ _, h
  | .bool _, .letE _ _ _, h | .bool _, .seq _, h | .bool _, .installPolicy _, h
  | .quote _, .num _, h | .quote _, .bool _, h | .quote _, .var _, h
  | .quote _, .ifte _ _ _, h | .quote _, .lam _ _, h | .quote _, .app _, h
  | .quote _, .set _ _, h | .quote _, .em _, h | .quote _, .primApp _ _, h
  | .quote _, .letE _ _ _, h | .quote _, .seq _, h | .quote _, .installPolicy _, h
  | .var _, .num _, h | .var _, .bool _, h | .var _, .quote _, h
  | .var _, .ifte _ _ _, h | .var _, .lam _ _, h | .var _, .app _, h
  | .var _, .set _ _, h | .var _, .em _, h | .var _, .primApp _ _, h
  | .var _, .letE _ _ _, h | .var _, .seq _, h | .var _, .installPolicy _, h
  | .ifte _ _ _, .num _, h | .ifte _ _ _, .bool _, h | .ifte _ _ _, .quote _, h
  | .ifte _ _ _, .var _, h | .ifte _ _ _, .lam _ _, h | .ifte _ _ _, .app _, h
  | .ifte _ _ _, .set _ _, h | .ifte _ _ _, .em _, h
  | .ifte _ _ _, .primApp _ _, h | .ifte _ _ _, .letE _ _ _, h
  | .ifte _ _ _, .seq _, h | .ifte _ _ _, .installPolicy _, h
  | .lam _ _, .num _, h | .lam _ _, .bool _, h | .lam _ _, .quote _, h
  | .lam _ _, .var _, h | .lam _ _, .ifte _ _ _, h | .lam _ _, .app _, h
  | .lam _ _, .set _ _, h | .lam _ _, .em _, h | .lam _ _, .primApp _ _, h
  | .lam _ _, .letE _ _ _, h | .lam _ _, .seq _, h | .lam _ _, .installPolicy _, h
  | .app _, .num _, h | .app _, .bool _, h | .app _, .quote _, h
  | .app _, .var _, h | .app _, .ifte _ _ _, h | .app _, .lam _ _, h
  | .app _, .set _ _, h | .app _, .em _, h | .app _, .primApp _ _, h
  | .app _, .letE _ _ _, h | .app _, .seq _, h | .app _, .installPolicy _, h
  | .set _ _, .num _, h | .set _ _, .bool _, h | .set _ _, .quote _, h
  | .set _ _, .var _, h | .set _ _, .ifte _ _ _, h | .set _ _, .lam _ _, h
  | .set _ _, .app _, h | .set _ _, .em _, h | .set _ _, .primApp _ _, h
  | .set _ _, .letE _ _ _, h | .set _ _, .seq _, h | .set _ _, .installPolicy _, h
  | .em _, .num _, h | .em _, .bool _, h | .em _, .quote _, h
  | .em _, .var _, h | .em _, .ifte _ _ _, h | .em _, .lam _ _, h
  | .em _, .app _, h | .em _, .set _ _, h | .em _, .primApp _ _, h
  | .em _, .letE _ _ _, h | .em _, .seq _, h | .em _, .installPolicy _, h
  | .primApp _ _, .num _, h | .primApp _ _, .bool _, h
  | .primApp _ _, .quote _, h | .primApp _ _, .var _, h
  | .primApp _ _, .ifte _ _ _, h | .primApp _ _, .lam _ _, h
  | .primApp _ _, .app _, h | .primApp _ _, .set _ _, h
  | .primApp _ _, .em _, h | .primApp _ _, .letE _ _ _, h
  | .primApp _ _, .seq _, h | .primApp _ _, .installPolicy _, h
  | .letE _ _ _, .num _, h | .letE _ _ _, .bool _, h
  | .letE _ _ _, .quote _, h | .letE _ _ _, .var _, h
  | .letE _ _ _, .ifte _ _ _, h | .letE _ _ _, .lam _ _, h
  | .letE _ _ _, .app _, h | .letE _ _ _, .set _ _, h
  | .letE _ _ _, .em _, h | .letE _ _ _, .primApp _ _, h
  | .letE _ _ _, .seq _, h | .letE _ _ _, .installPolicy _, h
  | .seq _, .num _, h | .seq _, .bool _, h | .seq _, .quote _, h
  | .seq _, .var _, h | .seq _, .ifte _ _ _, h | .seq _, .lam _ _, h
  | .seq _, .app _, h | .seq _, .set _ _, h | .seq _, .em _, h
  | .seq _, .primApp _ _, h | .seq _, .letE _ _ _, h
  | .seq _, .installPolicy _, h
  | .installPolicy _, .num _, h | .installPolicy _, .bool _, h
  | .installPolicy _, .quote _, h | .installPolicy _, .var _, h
  | .installPolicy _, .ifte _ _ _, h | .installPolicy _, .lam _ _, h
  | .installPolicy _, .app _, h | .installPolicy _, .set _ _, h
  | .installPolicy _, .em _, h | .installPolicy _, .primApp _ _, h
  | .installPolicy _, .letE _ _ _, h | .installPolicy _, .seq _, h =>
      by simp [Expr.beq] at h

theorem expr_list_beq_eq : ∀ (xs ys : List Expr), exprListBeq xs ys = true → xs = ys
  | [],      [],      _ => rfl
  | _ :: _,  [],      h => by simp [exprListBeq] at h
  | [],      _ :: _,  h => by simp [exprListBeq] at h
  | x :: xs, y :: ys, h => by
      simp only [exprListBeq, Bool.and_eq_true] at h
      exact (expr_beq_eq x y h.1) ▸ (expr_list_beq_eq xs ys h.2) ▸ rfl

theorem env_beq_eq : ∀ (a b : Env), Env.beq a b = true → a = b
  | .nil,           .nil,           _ => rfl
  | .nil,           .cons _ _ _,    h => by simp [Env.beq] at h
  | .cons _ _ _,    .nil,           h => by simp [Env.beq] at h
  | .cons k₁ i₁ r₁, .cons k₂ i₂ r₂, h => by
      simp only [Env.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ h.1.2 ▸ (env_beq_eq r₁ r₂ h.2) ▸ rfl

end

/-! ## Reflexivity of structural beq -/

mutual

theorem val_beq_self : ∀ (a : Val), Val.beq a a = true
  | .num _ => by simp [Val.beq]
  | .bool _ => by simp [Val.beq]
  | .nilV => rfl
  | .sym _ => by simp [Val.beq]
  | .prim _ => by simp [Val.beq]
  | .builtinBaseApply => rfl
  | .cons x y => by
      unfold Val.beq
      rw [val_beq_self x, val_beq_self y]; rfl
  | .closure ps body cenv => by
      unfold Val.beq
      rw [expr_beq_self body, env_beq_self cenv]
      simp

theorem expr_beq_self : ∀ (a : Expr), Expr.beq a a = true
  | .num _ => by simp [Expr.beq]
  | .bool _ => by simp [Expr.beq]
  | .quote v => by unfold Expr.beq; exact val_beq_self v
  | .var _ => by simp [Expr.beq]
  | .ifte c t e => by
      unfold Expr.beq
      rw [expr_beq_self c, expr_beq_self t, expr_beq_self e]; rfl
  | .lam ps body => by
      unfold Expr.beq
      rw [expr_beq_self body]; simp
  | .app es => by unfold Expr.beq; exact expr_list_beq_self es
  | .set x e => by
      unfold Expr.beq
      rw [expr_beq_self e]; simp
  | .em b => by unfold Expr.beq; exact expr_beq_self b
  | .primApp f as => by
      unfold Expr.beq
      rw [expr_beq_self f, expr_list_beq_self as]; rfl
  | .letE x e b => by
      unfold Expr.beq
      rw [expr_beq_self e, expr_beq_self b]; simp
  | .seq es => by unfold Expr.beq; exact expr_list_beq_self es
  | .installPolicy _ => by simp [Expr.beq]

theorem expr_list_beq_self : ∀ (xs : List Expr), exprListBeq xs xs = true
  | [] => rfl
  | x :: xs => by
      unfold exprListBeq
      rw [expr_beq_self x, expr_list_beq_self xs]; rfl

theorem env_beq_self : ∀ (a : Env), Env.beq a a = true
  | .nil => rfl
  | .cons k i r => by
      unfold Env.beq
      rw [env_beq_self r]; simp

end

abbrev Heap := List Val

/-- The mutation site context the policy gate sees at admission
    time. The runtime `.set x e` populates this from the live state
    just before invoking the gate; the policy can therefore inspect
    the heap (e.g., for `OrigBoundIn`-style install-protocol facts),
    the target name (to restrict admission to specific binding
    names like `"base-apply"`), or the captured-env structure of
    the proposed value. -/
structure MutationCtx where
  target  : String   -- the name being mutated (`x` in `(set! x e)`)
  heap    : Heap     -- the heap at the moment of the gate check
                     -- (post-RHS evaluation but pre-update)
  env     : Env      -- the env in which the `.set` was evaluated
  metaEnv : Env      -- the meta-env in scope
  index   : Nat      -- the heap index `target` resolves to

/-- A policy decides whether to admit a meta-env mutation, given the
    mutation context and the old / new values.

    The library of concrete policies and their soundness theorems
    lives in `LeanBlack/Policies.lean`. -/
abbrev BlackPolicy := MutationCtx → Val → Val → Bool

/-- Soundness of a policy w.r.t. an arbitrary architectural floor `P`.
    The canonical instance is `P = ConservativeExt` (defined in
    `Policies.lean`); other instances (termination preservation,
    refinement of a spec, ...) live in the same library. -/
def BlackPolicy.Sound (P : Val → Val → Prop) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true → P old new

abbrev PolicyTable := List BlackPolicy

structure RunState where
  heap   : Heap
  policy : BlackPolicy

def Env.lookup : Env → String → Option Nat
  | .nil, _ => none
  | .cons k idx rest, name => if k == name then some idx else rest.lookup name

/-- True iff `x` resolves to the same heap-cell index in both `env`
    and `metaEnv`. This is the architectural marker: mutations that
    hit a meta-env binding go through the policy gate. -/
def isMetaMutation (x : String) (env metaEnv : Env) : Bool :=
  match env.lookup x, metaEnv.lookup x with
  | some i₁, some i₂ => i₁ == i₂
  | _, _             => false

def Heap.alloc (h : Heap) (v : Val) : Heap × Nat := (h ++ [v], h.length)

def Heap.update : Heap → Nat → Val → Heap
  | [],       _,     _ => []
  | _ :: t,   0,     v => v :: t
  | x :: t,   n + 1, v => x :: Heap.update t n v

def listToVal : List Val → Val
  | []      => .nilV
  | x :: xs => .cons x (listToVal xs)

def valToList : Val → Option (List Val)
  | .nilV       => some []
  | .cons x xs  =>
      match valToList xs with
      | some l => some (x :: l)
      | none   => none
  | _           => none

def mulConsList : Val → Option Int
  | .nilV               => some 1
  | .cons (.num n) rest => (mulConsList rest).map (n * ·)
  | _                   => none

/-- Heap-independent values: contain no closure references, and so
    relate trivially to themselves under any pair of heaps. Used to
    constrain `.quote` to literals, which is the only practical
    use-case (programs only `.quote` atoms / cons-lists of atoms). -/
def closedValB : Val → Bool
  | .num _              => true
  | .bool _             => true
  | .nilV               => true
  | .sym _              => true
  | .prim _             => true
  | .builtinBaseApply   => true
  | .cons x y           => closedValB x && closedValB y
  | .closure _ _ _      => false

/-- Each primitive's behavior is split into its own helper. The top-level
    `applyPrim` then dispatches on `name`. This shape lets Lean's match
    compiler generate equational lemmas for each helper independently
    (rather than failing on one giant nested match), which is required
    for clean per-prim case analysis in proofs. -/
def applyPrim_plus : List Val → Option Val
  | [.num a, .num b] => some (.num (a + b))
  | _                => none

def applyPrim_minus : List Val → Option Val
  | [.num a, .num b] => some (.num (a - b))
  | _                => none

def applyPrim_times : List Val → Option Val
  | [.num a, .num b] => some (.num (a * b))
  | _                => none

def applyPrim_mulList : List Val → Option Val
  | [v] => (mulConsList v).map (.num ·)
  | _   => none

def applyPrim_eq : List Val → Option Val
  | [.num a, .num b] => some (.bool (a == b))
  | _                => none

def applyPrim_numQ : List Val → Option Val
  | [.num _] => some (.bool true)
  | [_]      => some (.bool false)
  | _        => none

def applyPrim_boolQ : List Val → Option Val
  | [.bool _] => some (.bool true)
  | [_]       => some (.bool false)
  | _         => none

def applyPrim_closureQ : List Val → Option Val
  | [.closure _ _ _] => some (.bool true)
  | [_]              => some (.bool false)
  | _                => none

def applyPrim_primQ : List Val → Option Val
  | [.prim _] => some (.bool true)
  | [_]       => some (.bool false)
  | _         => none

def applyPrim_cons : List Val → Option Val
  | [a, b] => some (.cons a b)
  | _      => none

def applyPrim_car : List Val → Option Val
  | [.cons a _] => some a
  | _           => none

def applyPrim_cdr : List Val → Option Val
  | [.cons _ b] => some b
  | _           => none

def applyPrim_nullQ : List Val → Option Val
  | [.nilV] => some (.bool true)
  | [_]     => some (.bool false)
  | _       => none

def applyPrim (name : String) (args : List Val) : Option Val :=
  if name = "+" then applyPrim_plus args
  else if name = "-" then applyPrim_minus args
  else if name = "*" then applyPrim_times args
  else if name = "mul-list" then applyPrim_mulList args
  else if name = "=" then applyPrim_eq args
  else if name = "num?" then applyPrim_numQ args
  else if name = "bool?" then applyPrim_boolQ args
  else if name = "closure?" then applyPrim_closureQ args
  else if name = "prim?" then applyPrim_primQ args
  else if name = "cons" then applyPrim_cons args
  else if name = "car" then applyPrim_car args
  else if name = "cdr" then applyPrim_cdr args
  else if name = "null?" then applyPrim_nullQ args
  else none

mutual
def eval (fuel : Nat) (ptable : PolicyTable) (exp : Expr)
    (env metaEnv : Env) (s : RunState) : Option (Val × RunState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i        => some (.num i, s)
    | .bool b       => some (.bool b, s)
    | .quote v      => if closedValB v then some (v, s) else none
    | .var x        =>
        match env.lookup x with
        | some idx => match s.heap[idx]? with
                      | some v => some (v, s)
                      | none   => none
        | none     => none
    | .ifte c t e   =>
        match eval n ptable c env metaEnv s with
        | some (.bool false, s') => eval n ptable e env metaEnv s'
        | some (_,           s') => eval n ptable t env metaEnv s'
        | none                   => none
    | .lam ps body  => some (.closure ps body env, s)
    | .app exps     =>
        match exps with
        | []        => none
        | f :: args =>
            match eval n ptable f env metaEnv s with
            | none           => none
            | some (fv, s')  =>
                match evalList n ptable args env metaEnv s' with
                | none            => none
                | some (avs, s'') => applyVia n ptable fv avs metaEnv s''
    | .primApp f args =>
        match eval n ptable f env metaEnv s with
        | none          => none
        | some (fv, s') =>
            match evalList n ptable args env metaEnv s' with
            | none            => none
            | some (avs, s'') => applyDirect n ptable fv avs metaEnv s''
    | .set x e      =>
        -- Freeze the gate at the start of `.set`, *before* `e`
        -- evaluates. Otherwise an `installPolicy`-bearing RHS could
        -- downgrade `s.policy` mid-evaluation and authorize itself
        -- under the looser policy. See `GOTCHAS.md` #1.
        let gate := s.policy
        match eval n ptable e env metaEnv s with
        | none         => none
        | some (v, s') =>
            match env.lookup x with
            | none     => none
            | some idx =>
                if isMetaMutation x env metaEnv then
                  -- Meta-env mutation: gate via the *frozen* policy,
                  -- with the live mutation context so the policy can
                  -- inspect the heap, target name, etc.
                  match s'.heap[idx]? with
                  | none        => none
                  | some oldVal =>
                      let ctx : MutationCtx :=
                        { target := x, heap := s'.heap, env := env,
                          metaEnv := metaEnv, index := idx }
                      if gate ctx oldVal v then
                        some (.bool true, { s' with heap := s'.heap.update idx v })
                      else
                        some (.bool false, s')
                else
                  -- Plain mutation: not gated. Returns true uniformly.
                  some (.bool true, { s' with heap := s'.heap.update idx v })
    | .em body      =>
        -- body runs with metaEnv as its env (so `base-apply` is in
        -- scope by name and `set!`-able from inside). Stage-1: meta-
        -- env-of-meta is the same metaEnv.
        eval n ptable body metaEnv metaEnv s
    | .letE x e body =>
        match eval n ptable e env metaEnv s with
        | none         => none
        | some (v, s') =>
            let (h'', idx) := s'.heap.alloc v
            eval n ptable body (.cons x idx env) metaEnv { s' with heap := h'' }
    | .seq exps     =>
        match exps with
        | []         => some (.nilV, s)
        | [e]        => eval n ptable e env metaEnv s
        | e :: rest  =>
            match eval n ptable e env metaEnv s with
            | none          => none
            | some (_, s')  => eval n ptable (.seq rest) env metaEnv s'
    | .installPolicy idx =>
        match ptable[idx]? with
        | some newPolicy => some (.bool true, { s with policy := newPolicy })
        | none           => some (.bool false, s)

def evalList (fuel : Nat) (ptable : PolicyTable) (exps : List Expr)
    (env metaEnv : Env) (s : RunState) : Option (List Val × RunState) :=
  match fuel with
  | 0     => none
  | n + 1 =>
    match exps with
    | []        => some ([], s)
    | e :: rest =>
        match eval n ptable e env metaEnv s with
        | none         => none
        | some (v, s') =>
            match evalList n ptable rest env metaEnv s' with
            | none           => none
            | some (vs, s'') => some (v :: vs, s'')

/-- Application via the meta-env's `base-apply`. The hinge of the
    causal-connection property: every Black-level application goes
    through whatever value is bound to `base-apply` in the current
    meta-env. -/
def applyVia (fuel : Nat) (ptable : PolicyTable) (op : Val) (args : List Val)
    (metaEnv : Env) (s : RunState) : Option (Val × RunState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match metaEnv.lookup "base-apply" with
    | none     => applyDirect n ptable op args metaEnv s
    | some idx =>
        match s.heap[idx]? with
        | none                       => none
        | some .builtinBaseApply     => applyDirect n ptable op args metaEnv s
        | some baseApply             =>
            applyDirect n ptable baseApply [op, listToVal args] metaEnv s

/-- Direct application — bypasses base-apply lookup. Used by the
    builtin dispatcher and by `prim-apply` (Black's `primitive-EM`
    analog: replacement closures use it to call captured originals
    without infinite regress). -/
def applyDirect (fuel : Nat) (ptable : PolicyTable) (op : Val) (args : List Val)
    (metaEnv : Env) (s : RunState) : Option (Val × RunState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match op with
    | .closure ps body cenv =>
        if ps.length != args.length then none else
          let (h', env') := args.zip ps |>.foldl
            (fun (acc : Heap × Env) (vp : Val × String) =>
              let (hh, ee) := acc
              let (hh', idx) := hh.alloc vp.1
              (hh', .cons vp.2 idx ee))
            (s.heap, cenv)
          eval n ptable body env' metaEnv { s with heap := h' }
    | .prim name =>
        match applyPrim name args with
        | some v => some (v, s)
        | none   => none
    | .builtinBaseApply =>
        match args with
        | [actualOp, operandsList] =>
            match valToList operandsList with
            | some operands => applyDirect n ptable actualOp operands metaEnv s
            | none          => none
        | _ => none
    | _ => none
end

/-! ## Initial state -/

def buildBindings (pairs : List (String × Val)) : Env × Heap :=
  pairs.foldl
    (fun (acc : Env × Heap) (kv : String × Val) =>
      let (env, h) := acc
      let (h', idx) := h.alloc kv.2
      (.cons kv.1 idx env, h'))
    (.nil, [])

def initBaseEnv : Env × Heap :=
  buildBindings
    [ ("+",        .prim "+")
    , ("-",        .prim "-")
    , ("*",        .prim "*")
    , ("=",        .prim "=")
    , ("num?",     .prim "num?")
    , ("bool?",    .prim "bool?")
    , ("closure?", .prim "closure?")
    , ("prim?",    .prim "prim?")
    , ("cons",     .prim "cons")
    , ("car",      .prim "car")
    , ("cdr",      .prim "cdr")
    , ("null?",    .prim "null?")
    , ("mul-list", .prim "mul-list")
    ]

/-- The default policy admits every mutation. Useful for demos that
    show the un-governed tower's failure modes (a malicious
    modification that breaks base-level arithmetic). Not sound for
    any non-trivial floor `P`; not in the verified table. -/
def acceptAllPolicy : BlackPolicy := fun _ _ _ => true

/-- Initial state: user env has the standard primitives bound;
    meta-env is the user env with `"base-apply" ↦ builtinBaseApply`
    on top, so closures created inside `(em ...)` see the user
    primitives in their captured env *and* have `base-apply`
    accessible by name and `set!`-able. -/
def initState (defaultPolicy : BlackPolicy := acceptAllPolicy) :
    Env × Env × RunState :=
  let (userEnv, h0) := initBaseEnv
  let (h1, idx)    := h0.alloc .builtinBaseApply
  let metaEnv      := Env.cons "base-apply" idx userEnv
  (userEnv, metaEnv, { heap := h1, policy := defaultPolicy })

def evalProgram (fuel : Nat) (ptable : PolicyTable) (e : Expr)
    (defaultPolicy : BlackPolicy := acceptAllPolicy) : Option Val :=
  let (env, metaEnv, s) := initState defaultPolicy
  (eval fuel ptable e env metaEnv s).map Prod.fst

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

abbrev Heap := List Val

/-- A policy decides whether to admit a meta-env mutation, given the
    old value at the heap cell and the new value being written.

    The library of concrete policies and their soundness theorems
    lives in `LeanBlack/Policies.lean`. -/
abbrev BlackPolicy := Val → Val → Bool

/-- Soundness of a policy w.r.t. an arbitrary architectural floor `P`.
    The canonical instance is `P = ConservativeExt` (defined in
    `Policies.lean`); other instances (termination preservation,
    refinement of a spec, ...) live in the same library. -/
def BlackPolicy.Sound (P : Val → Val → Prop) (p : BlackPolicy) : Prop :=
  ∀ old new, p old new = true → P old new

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

def applyPrim : String → List Val → Option Val
  | "+",        [.num a, .num b]   => some (.num (a + b))
  | "-",        [.num a, .num b]   => some (.num (a - b))
  | "*",        [.num a, .num b]   => some (.num (a * b))
  | "mul-list", [v]                => (mulConsList v).map (.num ·)
  | "=",        [.num a, .num b]   => some (.bool (a == b))
  | "num?",     [.num _]           => some (.bool true)
  | "num?",     [_]                => some (.bool false)
  | "bool?",    [.bool _]          => some (.bool true)
  | "bool?",    [_]                => some (.bool false)
  | "closure?", [.closure _ _ _]   => some (.bool true)
  | "closure?", [_]                => some (.bool false)
  | "prim?",    [.prim _]          => some (.bool true)
  | "prim?",    [_]                => some (.bool false)
  | "cons",     [a, b]             => some (.cons a b)
  | "car",      [.cons a _]        => some a
  | "cdr",      [.cons _ b]        => some b
  | "null?",    [.nilV]            => some (.bool true)
  | "null?",    [_]                => some (.bool false)
  | _,          _                  => none

mutual
def eval (fuel : Nat) (ptable : PolicyTable) (exp : Expr)
    (env metaEnv : Env) (s : RunState) : Option (Val × RunState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i        => some (.num i, s)
    | .bool b       => some (.bool b, s)
    | .quote v      => some (v, s)
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
        match eval n ptable e env metaEnv s with
        | none         => none
        | some (v, s') =>
            match env.lookup x with
            | none     => none
            | some idx =>
                if isMetaMutation x env metaEnv then
                  -- Meta-env mutation: gate via current policy.
                  match s'.heap[idx]? with
                  | none        => none
                  | some oldVal =>
                      if s'.policy oldVal v then
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
def acceptAllPolicy : BlackPolicy := fun _ _ => true

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

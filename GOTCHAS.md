# Gotchas

Subtleties in this codebase that aren't documented in the
load-bearing places (`README` / `DESIGN`) but will trip you up
if you extend it. Living document — add as more get found.

Organized by *what kind* of trap each is. Concrete code
references where applicable.

---

## Semantics traps

### 1. TOCTOU at `.set`'s policy gate (FIXED)

`Black.lean`'s `.set x e` now snapshots `s.policy` at the start
of `.set`, *before* `e` evaluates:

```lean
| .set x e =>
    let gate := s.policy            -- ← frozen at start of .set
    match eval n ptable e env metaEnv s with
    | some (v, s') =>
        ...
        if gate ctx oldVal v then ...   -- uses the snapshot
```

This prevents the classic time-of-check-to-time-of-use attack
where the RHS calls `installPolicy idx_acceptAll` to downgrade
the gate before authorizing itself. `installPolicy` calls in `e`
still take effect post-`.set` (the resulting `s'.policy` reflects
them); they just don't authorize the current `.set`.

Tested in `Smoke.lean` scene 3 (`test_strict_freeze_admits_install`
+ `test_strict_freeze_post_install_locked`): an
`installPolicy idx_rejectAll` mid-RHS doesn't block the install
itself but does lock down subsequent mutations.

### 2. `isMetaMutation` is *index*-equality, not *name*-equality

```lean
def isMetaMutation (x : String) (env metaEnv : Env) : Bool :=
  match env.lookup x, metaEnv.lookup x with
  | some i₁, some i₂ => i₁ == i₂
  | _, _             => false
```

The check is "do `env` and `metaEnv` agree on the *heap cell* `x`
points to?" — not "is the name `x` bound in both?". Shadowing
`x` with a `letE` *in the env but not the metaEnv* makes
`isMetaMutation x env metaEnv = false`, so the `.set` becomes
plain mutation (not gated).

This is the right semantics for Black's reflection model — meta-
mutations are precisely those that hit the meta-env's cells. But
when reading the code, "is this a meta-mutation?" feels like a
name-level question and is actually a heap-cell-level question.

### 3. `Heap.alloc` returns the *old* length as the new index

```lean
def Heap.alloc (h : Heap) (v : Val) : Heap × Nat := (h ++ [v], h.length)
```

`idx = h.length` (length **before** append), not `h.length`
**after**. So the cell at the returned index is the freshly
appended one. Off-by-one trap when reasoning about `(h ++ [v]).length`
vs `h.length + 1`.

### 4. `Val.builtinBaseApply` is its own `Val` constructor, not a closure

```lean
inductive Val where
  | num               : Int → Val
  | bool              : Bool → Val
  | nilV              : Val
  | cons              : Val → Val → Val
  | sym               : String → Val
  | prim              : String → Val
  | closure           : List String → Expr → Env → Val
  | builtinBaseApply  : Val          -- ← its own constructor
```

`ValVis_aux` between `.builtinBaseApply` and a `.closure ...`
value is **`False`** by inversion — they're different
constructors. This is exactly why the headline operational theorem
concludes `ValVis_weak` rather than `ValVis`: `multnExactPolicy`
admits replacing `.builtinBaseApply` with a multn closure, which is
operationally CE-extending but structurally non-`ValVis`-related.
The relaxed `ValVis_weak` allows different constructors when the
behavioral observation matches; see `WAND.md` for the full story.

### 5. `applyDirect`'s `.builtinBaseApply` arm expects unwrapped args

```lean
def applyDirect ... :=
  match op with
  | .builtinBaseApply =>
      match args with
      | [actualOp, operandsList] =>          -- ← exactly two args
          match valToList operandsList with
          | some operands => applyDirect ... actualOp operands ...
```

The args list is `[op, listToVal operands]` — a wrapped form. User-level
`(f x y)` calls go through `applyVia` (which wraps); only
post-replacement closure calls (where the multn closure forwards
to `(orig op args)`) hit this arm directly. Easy to confuse with
the user-level call path.

### 6. `installPolicy` silently no-ops on out-of-bounds index

```lean
| .installPolicy idx =>
    match ptable[idx]? with
    | some newPolicy => some (.bool true, ...)
    | none           => some (.bool false, s)   -- ← silent
```

`installPolicy 999` returns `(.bool false, s)` and the caller has
no way to distinguish "policy index doesn't exist" from "policy
existed but admit-rejected by something else." If you add a new
table entry, double-check the index numbering matches the
`Policy.idx_*` constants in `Policies.lean`.

### 7. `em` is single-stage meta

`(em body)` runs `body` with `metaEnv` as the env. There's no
*meta-of-meta* level — the meta-env's meta-env is just the same
metaEnv:

```lean
| .em body =>
    eval n ptable body metaEnv metaEnv s   -- both env and metaEnv
                                            -- become metaEnv
```

Black's full architecture has infinite meta-levels; this
mechanization collapses to two. Programs assuming `(em (em ...))`
gives a fresh meta-meta-env will be surprised.

---

## Proof-architecture traps

### 8. `HeapExt` is prefix-only

```lean
def HeapExt (s_a s_b : RunState) : Prop :=
  ∃ extras, s_b.heap = s_a.heap ++ extras
```

Same-side heap-monotonicity is **prefix extension only**, not
update-allowed. Any in-place mutation (e.g., `Heap.update` from a
successful `.set`) violates this — same-length heaps differ at one
index, so `extras = []` is required, but the heaps aren't equal.
The `.set` case in `frame.eval` is closed via the cross-side
`HeapEvolution` relation (which captures cross-side env- and val-
bisim preservation across an in-place update), not via `HeapExt`.

### 9. `StateExt` is *just* policy equality, not heap-prefix

```lean
def StateExt (s_a s_b : RunState) : Prop := s_a.policy = s_b.policy
```

An earlier draft had `StateExt` carry an `∃ extras, s_b.heap =
s_a.heap ++ extras` component too. That was *provably wrong*:
independent same-side allocations on the two bisim sides give
heaps that aren't prefix-related. The cross-side heap relation
lives instead in `EnvVis` / `ValVis` claims about specific values
(which take two heaps without needing a prefix relation).

### 10. `ValVis` requires *syntactically equal* closure bodies

```lean
| n+1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b, _, _ =>
    ps_a = ps_b ∧ body_a = body_b ∧ ...   -- ← body equality
```

Two *operationally equivalent* closures with different bodies
(say, after a refactoring or compiler pass) are **not**
`ValVis`-related. This is fine for fuel-bisim within a single
language (which is what we use it for), but the moment you try
to relate source and compiled code, or relate two refactored
versions of the same operator, `ValVis` is the wrong relation.
The replacement is a step-indexed logical relation — see
`FUTURE.md` / *Redoing it on different foundations / Logical
relations*.

### 11. Depth-indexed `ValVis_aux` — don't define `ValVis` as a fixed point

The mutual recursion `ValVis ↔ EnvVis` (closure case looks up
heap values, which need to be `ValVis`-related) is **not
structurally founded** — Lean's structural-recursion checker
can't see termination. The fix is depth-indexing:
`ValVis_aux : Nat → ...`, with `ValVis := ∀ n, ValVis_aux n`.

If you try to inline-define `ValVis` directly without the depth-
indexed scaffolding, Lean rejects it as not-structurally-decreasing.
Don't fight the depth-indexing; it's the standard CakeML approach
for exactly this reason.

### 12. The `frame.eval` `.set` case is closed (FIXED)

The `.set` case of `frame.eval` is now fully proved using a
cross-side `HeapEvolution` infrastructure plus `PolicyRespectsBisim`,
`env_eq`, and `heap_len_eq` invariants on `WFCtx`. The proof
threads these invariants through the framing theorem and uses a
mutual depth induction `ValVis_aux_update` / `EnvVis_aux_update`
to handle in-place cell updates.

`multnExact_CE_nonnum_case`'s historical asymmetric framing
setup `(s, s_alloc)` (incompatible with `WFCtx.heap_len_eq`) is
resolved via the functional-shift prefix-extension lemma
`applyDirect_heap_extend_via_shift` (no `WFCtx`-style cross-side
invariants; uses `shift_respect`'s joint shift-commutativity).

### 13. Closure-case args allocate via foldl on `args.zip ps`

```lean
let (heap', cenv') := args.zip ps |>.foldl allocStep (s.heap, cenv)
```

When proving things about closure calls in `frame.applyDirect`'s
closure case, the resulting heap is `s.heap ++ [args[0], args[1], ...]`
(by `List.append_assoc` chain) and the env is
`.cons p_n (s.heap.length + n - 1) (.cons p_{n-1} (s.heap.length + n - 2) (... (.cons p_0 s.heap.length cenv) ...))`
(*reversed* binding order from a naive read). The `alloc_chain_bisim`
lemma encapsulates the necessary invariants; reach for it before
unfolding the foldl manually.

---

## Runner / soundness-boundary traps

### 14. The active runner policy is `multnExactPolicy` (FIXED)

`Elab.lean` and `Runner.lean` now use `multnExactPolicy`
(`idx_multnExact = 2`), which is the CE-sound strict-shape
policy. The runner's "ADMITTED" verdict now means: the runtime
gate verified `target = "base-apply"`, the strict multn shape,
and the install-protocol facts (`OrigBoundIn`, `NumQBoundIn`)
against `MutationCtx`. The bridge lemma
`multnExactPolicy_implies_InstallFacts` proves that this matches
exactly what the headline soundness theorem requires.

Previously (pre-Phase-A): `Elab.lean` hardcoded `installPolicy 1`
(numGuard, loose, not CE-sound). The runner's verdict didn't
imply CE-soundness. README's *Concession 0* documented this.

### 15. `numGuardPolicy`'s else-branch is unconstrained

```lean
def numGuardPolicy : BlackPolicy := fun _old new =>
  match new with
  | .closure [_, _] (.ifte (.primApp (.var "num?") [.var _]) _ _) _ => true
  --                                                          ^   ^
  --                                                       any then,
  --                                                       any else
```

A closure with a constant else-branch (e.g., `.num 0`) *passes*
`numGuardPolicy` and breaks CE on non-numeric operators. This is
why `numGuardPolicy` is a coarse filter, not a soundness gate.
Easy to mistake "matches the shape" for "behaves correctly."

### 16. `BlackPolicy` is now context-aware (FIXED)

```lean
structure MutationCtx where
  target  : String
  heap    : Heap
  env     : Env
  metaEnv : Env
  index   : Nat

abbrev BlackPolicy := MutationCtx → Val → Val → Bool
```

The gate now sees the full mutation context. `multnExactPolicy`
exploits this to check `OrigBoundIn` and `NumQBoundIn` against
`ctx.heap` at admission time, plus restrict admission to
`target = "base-apply"`. The bridge lemma
`multnExactPolicy_implies_InstallFacts` in `Policies.lean` proves
that runtime admission discharges the install-protocol facts the
headline soundness theorem requires.

Tested in `Smoke.lean` scene 3 (multiple cases — shadowed-`orig`,
wrong target, `numGuard`-shaped malicious — all refused).

### 17. `Elab.lean`'s splice-and-elaborate is not a security boundary

`Elab.lean` writes the LLM's output into a Lean source file and
runs `lake env lean --run`. This is **executing untrusted Lean**.
The "no commentary" prompt is not a constraint the LLM is forced
to obey. A model can emit `#eval ...`, top-level declarations,
side-effecting commands; they all run during elaboration. The
verdict-parser also reads stdout, which the model can influence.

If you're using this development as a security demo, the gate's
`Bool` decision is not the only TCB — the elaborator path is too.
Item 7 of `FUTURE.md` / *Hardening seam* (Black `Expr` parser /
JSON AST / sandboxed elab).

### 18. `mulConsList` returns `none` on any non-`.num` cons element

```lean
def mulConsList : Val → Option Int
  | .nilV               => some 1
  | .cons (.num n) rest => (mulConsList rest).map (n * ·)
  | _                   => none
```

A cons-list `(2 3 nil 4)` (with `.nilV` mid-list) returns `none`
— `mulConsList` requires `.cons` all the way down ending in `.nilV`,
with every cell `.num _`. So `(mul-list <heterogeneous-list>)`
fails silently. Important when constructing test inputs — the
multn body uses this primitive.

### 19. `Smoke.lean` exits non-zero on FAIL (recently added)

If you're adapting test patterns from elsewhere in the codebase
or adding new ones, note the `failureCount` ref machinery:

```lean
initialize failureCount : IO.Ref Nat ← IO.mkRef 0
...
def main : IO Unit := do
  ...
  if (← failureCount.get) > 0 then IO.Process.exit 1
```

`reportLine` / `reportPair` increment `failureCount` on
mismatch. If you add a new reporter, increment it too — silent
non-incrementing reporters break CI's trust in the test count.

---

## Build / toolchain traps

### 20. No mathlib

The `lakefile.lean` declares no mathlib dependency. List lemmas,
`getElem?` reasoning, and `Nat` arithmetic are all from `Init` /
`Std`. If you import a mathlib lemma without adding the dependency,
the build fails late (during proof elaboration) with a confusing
"unknown identifier" error.

If you want mathlib, add it explicitly — but expect a substantial
toolchain-fetch first build, and the docs claim a small footprint
that the dependency would invalidate.

### 21. `lean4:v4.20.0` toolchain pin

`lean-toolchain` pins `leanprover/lean4:v4.20.0`. Some Lean 4
tactics (`set`, certain `simp` extensions) work differently in
later toolchains. If you upgrade, expect to revisit the more
intricate proofs (especially `frame`'s `.app` and `.primApp`
cases, which use careful `simp only [eval]`-then-`rw` chains
keyed on specific match-arm shapes).

---

## How to add to this file

Found a non-obvious behavior? A bug that almost shipped because
no one had documented the assumption? An invariant that has to
hold for the proofs to go through but isn't named anywhere?

Add a numbered entry under the appropriate section, with:
- **Title** stating the trap concisely.
- **Code snippet** if applicable (5 lines max).
- **Why it's a trap** in 2–4 sentences.
- **What to do / pointer** to the right fix or further reading.

Keep entries short. The point is that someone debugging a
mysterious failure can grep this file for the symptom and land
on the gotcha.

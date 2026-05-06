# Path A — why `frame` is set-free

This document explains Path A: the design choice that closed the
`.set` sorry in the framing theorem. The phrase "set-free framing"
can sound like a workaround if you don't see why it is the
principled answer. This walkthrough shows why structural framing
*across* reflective `.set` is **provably false** for the policies
that make reflective mutation meaningful, and why the right
response is a *two-theorem* decomposition rather than fixing
`frame` to handle everything in one shot.

It assumes basic Lean 4 / programming-language-theory background
and reads cold (no need to have read `DESIGN.md` first).

---

## The setting

Black-style reflection makes the meta-environment *data*, not
metadata. Concretely:

- There's a heap cell whose contents is the value of `base-apply` —
  the function the interpreter consults for *every* application.
- The Black expression `(set! base-apply <new>)` mutates that cell.
- Every `(f x y)` therefore goes through whatever's currently in
  that cell. So you can install a new application semantics by
  mutating one heap location.

This is the "causal connection" property: meta-level changes
propagate to base-level dispatch through real heap mutation, not
through some indexed table that pretends to be a meta-level.

**The verified-governance question:** when may we admit such a
mutation? In the development, `multnExactPolicy` admits exactly
closures of a specific shape — `(λ (op args) (if (num? op) <multn>
(orig op args)))` — that conservatively extend the previous
`base-apply`. The headline theorem says: if `multnExactPolicy`
admits a `new` value, every program's behavior under `new`
conservatively extends its behavior under the original
`base-apply`.

To prove this, we need a *framing theorem*.

---

## The framing question

A framing theorem says, roughly: *"if the same expression runs on
two related states, the results are related."* The standard tool
is bisimulation. The natural definition (CakeML-style):

```
ValVis v_a v_b h_a h_b   -- v_a and v_b are bisim-related across heaps h_a, h_b
```

- For first-order values (numbers, booleans, atoms): `ValVis` is
  equality.
- For **closures**: two closures relate iff their bodies are
  *syntactically equal* and their captured environments are
  pointwise `ValVis`-related (Kumar 2016 §3.2 — the relation is
  *syntax-based data refinement*).

The framing theorem we want, schematically:

```
eval n exp env metaEnv s_a = some (r_a, s_a')   →
∃ r_b s_b',
  eval n exp env metaEnv s_b = some (r_b, s_b') ∧
  ValVis r_a r_b s_a'.heap s_b'.heap
```

— if `eval` succeeds on the a-side, it succeeds on the b-side
with a `ValVis`-related result.

For most expression forms this is straightforward induction on
fuel. The hard case is `.set`.

---

## What goes wrong at `.set`

Recall the `.set x e` clause of `eval`:

1. Evaluate `e` to get the new value `v`.
2. Look up `x` to get a heap index `idx`.
3. If `x` is a meta-mutation (`env` and `metaEnv` agree on `idx`),
   check `s.policy oldVal v`.
4. If the policy admits, mutate: `Heap.update s.heap idx v`.

`Heap.update` *replaces a cell in place*. It does **not** append.
So after a successful `.set`, the new heap has the same length but
differs from the old at one index.

Now run this through the framing theorem. The conclusion needs to
relate the post-states. The pre-Path-A `frame` postcondition was:

```
HeapExt s_a s_a' := ∃ extras, s_a'.heap = s_a.heap ++ extras
```

— *prefix extension*. After `.set`-accepted, `s_a'.heap` is **not**
a prefix extension of `s_a.heap`: same length, different at one
index. So `HeapExt s_a s_a'` is straightforwardly **false** in
this branch. Not unproven; provably false.

You might think: weaken `HeapExt` to admit in-place updates. Call
the weaker relation `HeapEvolves`. The natural definition:

```
HeapEvolves h h' :=
  h.length ≤ h'.length ∧
  ∀ i v, h[i]? = some v →
    ∃ v', h'[i]? = some v' ∧ ∀ n, ValVis_aux n v v' h h'
```

— heap may grow, and at every old index the new value is
`ValVis`-related to the old. That's the right shape; old bisim
claims about heap contents continue to hold.

For `HeapEvolves` to be preserved by `.set`-accept, **the policy
must admit only `ValVis`-related transitions**. Call this
`BisimSafe`:

```
BisimSafe (p) := ∀ old new h, p old new = true → ∀ n, ValVis_aux n old new h h
```

And here we hit the wall.

---

## The wall

`multnExactPolicy` admits the transition where:

- `old` = `.builtinBaseApply` (a tag — it's its **own** constructor
  in `Val`).
- `new` = `.closure ["op", "args"] body cenv` (the multn closure,
  a *different* `Val` constructor).

By inversion of `ValVis_aux`'s definition, two values with
**different constructors** are not `ValVis`-related at any non-zero
depth:

```
ValVis_aux (n+1) .builtinBaseApply (.closure _ _ _) _ _   ≡   False
```

So `multnExactPolicy` admits transitions that are *not* bisim-
respecting. **No heap makes them bisim-related**; this is not a
heap-state issue. A `BisimSafe` hypothesis on `multnExactPolicy`
is *unsatisfiable*.

This is not a quirk to engineer around. It is **the architectural
content of reflective mutation**.

---

## Why is this so?

`ValVis` is *structural*. It cares about constructor shape and
captured-environment contents. It's the right relation for:
- compiler correctness (where source closures map to target
  closures with syntactically equal bodies up to compilation), and
- fuel-bisim preservation in a single-language interpreter (where
  the same `eval` is run on two states).

`CE` (conservative extension) is *operational*. `new` CE-extends
`old` iff every `(op, operands)` where `old` succeeds, `new` also
succeeds with a related result. It's a *behavioral* predicate —
about what the value *does*, not what it *is*.

Reflective mutation is, by design, an **operational** substitution.
The whole point of installing a multn-shaped closure as the new
`base-apply` is that the closure *behaves equivalently to the
original on numeric operators, and conservatively extends it on
non-numerics*. That's an operational claim. Structurally,
`.builtinBaseApply` (a tag constructor) and a closure are
different kinds of value.

Demanding they be `ValVis`-related is demanding that operational
equivalence imply structural equivalence. It doesn't, by design —
the difference is exactly what makes reflection a real
substitution rather than a no-op.

---

## Three options

When we hit this wall, three responses:

### Option 1 — Make framing structural-only (rejected)

Add `BisimSafe` as a hypothesis. Prove framing-with-`HeapEvolves`
for `BisimSafe` policies. Result: a clean general theorem that
does **not** apply to `multnExactPolicy` (or any other policy that
admits operationally-equivalent-but-structurally-distinct
extensions).

The very policies that make reflection meaningful are excluded.
The theorem is real and applies to a class of policies (e.g.,
type-respecting policies that admit only same-constructor
extensions); it just has no client in this development.

This is documented in `FUTURE.md` as **Path B** — a useful
companion theorem if a `BisimSafe`-policy library ever materializes.

### Option 2 — Replace the relation (rejected)

Replace `ValVis` with a step-indexed *logical relation* — two
values relate iff they implement the same function (modulo CE).
`.builtinBaseApply` and the multn closure can now relate.
Framing across `.set` becomes provable.

This is the *deepest* fix. It's also a major rewrite of the
bisimulation infrastructure (~several thousand LOC), changes the
proof technique fundamentally, and most of the existing
`Bisim.lean` would be discarded.

This is documented in `FUTURE.md` as a *redo on different
foundations*. It's the right answer for a future development
whose goal includes uniform framing across reflective steps; it
is too expensive for the current artifact's scope.

### Option 3 — Don't try to frame `.set`. Frame the rest, and handle `.set` separately. (chosen)

Restrict `frame`'s domain to expressions *without* `.set`.
Reflective `.set` steps live **outside** `frame` — they're handled
by a *separate* theorem about the install protocol.

This is **Path A**.

---

## The Path A architecture

Two theorems, with a clean interface.

### Theorem 1 — `frame` (set-free framing)

For expressions in the *non-reflective sublanguage* — those
without `.set` — bisim-related inputs produce bisim-related
results. The `.set _ _` case of `eval` is *impossible* in `frame`'s
domain (the hypothesis `SetFreeExpr exp` rules it out by `False`,
discharged by case analysis on the Expr constructor).

### Theorem 2 — `multnExact_soundForCE_first_install` (install protocol)

At a clean state where the runner has admitted a
`multnExactPolicy`-shaped modification, the post-install behavior
conservatively extends the pre-install behavior. The proof uses
`frame` *internally*, but only on the **post-install user-call**:
the user is calling some operator `op` (e.g., `+`), and the
question is whether the user's call goes through to the right
primitive. That call does **not** contain `.set` (the user isn't
installing modifications mid-call), so `frame` applies.

```
                  headline theorem
              (CE soundness of an install)
                          ↓
              ┌──────────────────────────┐
              │  install-protocol step:  │
              │  the new closure's body  │
              │  on (op, operands)       │
              │  reduces to applying op  │
              │  to operands at the      │
              │  post-install state      │
              │                          │
              │  multn_closure_body_     │
              │     unfolds              │
              └──────────────────────────┘
                          ↓
              ┌──────────────────────────┐
              │  framing on the user     │
              │  call (set-free!) —      │
              │  bridge pre- and post-   │
              │  install state           │
              │                          │
              │  frame.applyDirect       │
              └──────────────────────────┘
```

`.set` *appears* at the top of this diagram — it's the install.
But `.set` does **not** appear inside `frame`'s domain. The split
is clean.

---

## What makes this principled, not a workaround

Three observations.

**(a) The split is mathematically forced, not chosen for
convenience.** Framing across reflective `.set` is *provably false*
for the policies of interest. There's no engineering trick around
this; you cannot have a single uniform framing theorem. So *either*
you weaken `frame` (Path A) *or* you change the bisimulation
relation entirely (Option 2). Path A weakens; Option 2 redoes.

**(b) The two theorems decompose along the right axis.** `frame` is
a property of the *language*; the install-protocol theorem is a
property of *the runner's discipline*. The runner says: "I admit a
modification only when it satisfies these install-time conditions."
The install-protocol theorem proves: "if those conditions hold, the
install is CE-safe." The two theorems compose because the runner
*invokes* the language at the user-call layer (uses `frame`) and
*governs* the language at the install layer (uses the install
protocol).

**(c) The runner naturally lives in `frame`'s domain.** Real Black
programs the runner cares about — user ops like `+`, the multn
closure body's operator dispatch, witness programs like
`(2 3 4)` — are all set-free. Reflective `.set` *only* appears at
install time, which the runner already treats as a special
governed event. The set-free restriction is exactly the runtime
invariant the runner maintains anyway.

---

## What predicates fall out

Three new predicates (Bisim.lean):

```
def SetFreeExpr : Expr → Prop      -- recursively true except `.set _ _`
def SetFreeVal  : Val → Prop       -- closures must have set-free bodies
def HeapSetFree : Heap → Prop      -- every cell holds a SetFreeVal
```

`frame`'s four mutual statements take them as hypotheses:

- Source-side branches (`eval`, `evalList`) take `SetFreeExpr exp`
  / `SetFreeListExpr exps`.
- Value-side branches (`applyDirect`, `applyVia`) take
  `SetFreeVal op` + `SetFreeListVal args`.
- `WFCtx` carries `HeapSetFree` on both sides.

The install-protocol theorem `multnExact_soundForCE_first_install`
takes a `SetFreeWF op operands s.heap` bundle as a side-condition.
The runner trivially establishes this — it constructs values from
`.lam` bodies of set-free Black source and atomic literals, never
from `.set`-bearing source.

The `.set _ _` case of `frame.eval` then closes by:

```
exact absurd h_setfree (by simp [SetFreeExpr])
```

— `SetFreeExpr (.set _ _) = False` by definition; contradiction.
The case is dispatched in one line.

---

## What you should believe after reading this

- Path A is *not* "we couldn't prove `.set` so we excluded it."
  The natural framing claim across `.set` is **false** for the
  policies that make reflective mutation meaningful — the
  exclusion is mathematically forced.
- Path A is *not* missing the install protocol. The install
  protocol is a *separate* theorem that uses `frame` on
  post-install user-calls.
- The set-free restriction is exactly what the runner already
  maintains. It's a precondition on the *static shape of
  programs*, not on their runtime state.
- The deeper fix (logical relations, Option 2) is real and is in
  `FUTURE.md`. Path A is the right choice for *this* development;
  logical relations would be the right choice for a future
  development whose goal includes uniform framing across
  reflective steps.

If you carry away one sentence: *the structural framing relation
and the operational reflection-extension relation are different
relations, and trying to make them the same is the bug — Path A
keeps them separate and composes them at the right layer.*

---

## Pointers

- `Bisim.lean` — `frame`, `SetFreeExpr` / `SetFreeVal` /
  `HeapSetFree`, the depth-indexed `ValVis_aux`, the four
  mutual `FrameStmt` branches.
- `Policies.lean` — `multnExact_soundForCE_first_install` (the
  headline install-protocol theorem); `InstallFacts` / `RuntimeWF`
  / `SetFreeWF` bundles; `multn_closure_body_unfolds` (the
  deterministic eval-trace lemma the install protocol uses to
  reduce the multn-closure call to the user-call before invoking
  `frame.applyDirect`).
- `DESIGN.md` — *Refinements / `.set` and Path A* for the same
  argument in the project's full-design context.
- `FUTURE.md` — *Generalizing the infrastructure / Path B as a
  companion theorem* (Option 1 written up as a follow-up) and
  *Redoing it on different foundations / Logical relations*
  (Option 2 written up as a follow-up).

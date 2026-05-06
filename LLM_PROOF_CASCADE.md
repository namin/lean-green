# The LLM-proof cascade

This document explains the **LLM-proof cascade** — the
architectural target the current `Bedrock`/`Elab`/`Runner` setup
is a stepping-stone toward. The phrase appears in `FUTURE.md` and
in the project's framing as "where can this go?"; this walkthrough
spells out what it actually means, why it's load-bearing, and
what would have to land before the current cascade becomes one.

It assumes you've read either `README.md` or the cascade's source
(`Runner.lean`, `Elab.lean`, `Bedrock.lean`).

---

## Today's cascade — propose-and-gate

The current architecture is a *structural* gate cascade:

```
LLM proposes a modification (a Black Expr)
                      ↓
Runner installs it under the active policy
                      ↓
Policy gate: BlackPolicy admits or refuses
                      ↓
If admitted, witness program runs to confirm causal connection
```

The gate is a `Bool`-valued function of `(old, new)`:

```lean
abbrev BlackPolicy := Val → Val → Bool
```

It decides admission *structurally* — pattern-matches on the new
value's shape. `multnExactPolicy`, for example, matches exactly
the strict multn-closure pattern with a delegating else-branch.

This is good architecture for what it is: the proposer (LLM) and
the gate (`BlackPolicy`) are completely separate kernels. The LLM
cannot generate proposals that bypass the gate; the gate cannot
generate proposals on its own. The runner is the only thing that
sees both.

But there's a real limitation. The structural gate can only check
*shape*. It can't check *meaning*. A proposal that matches the
shape but violates the install-protocol invariants (e.g., shadows
a captured `orig` to point somewhere unexpected) will pass the
gate. The shape is necessary but not sufficient for soundness.

---

## The proof-cascade extension

Make the LLM produce **two things**:

1. The **modification** — a Black `Expr` (as today).
2. A **soundness proof** — a Lean term whose type is the
   architectural floor applied to `(old, new)`.

The runner then type-checks both:

```
LLM proposes (modification, soundness-proof-script)
                      ↓
Runner elaborates `modification` as a Black Expr in a sandbox
Runner elaborates `proof-script` against the soundness goal
                      ↓
Lean kernel type-checks the proof
                      ↓
If both type-check: admit, install, run witness
Otherwise: reject with the type-checker's diagnostic
```

The gate is no longer a `Bool`-valued shape-matcher. It is a
**proof-checker**: a Lean kernel verifying a closed term has the
required type.

---

## Why this is interesting

Three things change.

### "The LLM cannot bypass the gate" becomes a Curry-Howard fact

Today, the LLM could, in principle, defeat `multnExactPolicy` by
emitting a structurally-conformant-but-semantically-broken
proposal — for instance, the shadowed-`orig` attack documented in
the README's *Concession 0*:

```scheme
(let ((orig 0))             ; ← shadowed: orig now points to .num 0
  (lambda (op args)
    (if (num? op)
        <multn>
        (orig op args))))   ; ← invokes the literal 0, not base-apply
```

This passes the structural gate. It violates the install-protocol
hypothesis `OrigBoundIn` and so falls outside the headline
theorem's domain — but the *runtime* gate doesn't see that.

In the proof-cascade, the LLM has to emit a closed term whose
type is something like `CE .builtinBaseApply new`. There is no
proof of a false proposition. If a Lean term has type `CE old new`
and Lean's kernel accepts it, then `CE old new` *holds*. The
shadowed-`orig` attack would now require the LLM to produce a
proof of a false proposition — which it cannot do, because no
such proof exists.

This is the gate becoming a security boundary by Curry-Howard
correspondence rather than by discipline. "The LLM cannot bypass
the gate" stops being a hopeful claim and becomes a type-theoretic
fact.

### The architectural floor `P` becomes a runner knob

Today, the floor is implicit. Each policy is sound for some `P`,
but the runtime treats the policy's `Bool` decision as opaque.
Tightening the floor (e.g., from "single-call result CE" to
"full-state CE preserving heap-validity and policy") requires
redesigning policies.

In the proof-cascade, the runner *publishes* the floor as the
proposition the LLM has to prove. Want a tighter floor? Publish a
tighter goal:

```lean
-- todays floor: single-call result CE
abbrev CE := ∀ ..., callAsBaseApply ... old ... = some r → ∃ r', ... ∧ ValVis ...

-- a tighter floor: full-state CE
abbrev CE_strong := CE ∧ s'.policy = s''.policy ∧ HeapValid s''.heap ∧ ...
```

The LLM's task changes accordingly; the runner doesn't change
shape. Adding a floor is a one-definition change, not a policy
redesign.

### Failure becomes informative

Today, a rejected proposal gives only `false` from the gate. The
LLM has no signal about *why*. Retry yields more guesses.

In the proof-cascade, a rejection comes with the **type-checker's
diagnostic**: unsolved goals, type mismatches, missing hypotheses.
The LLM can read these and revise the proof script with the
diagnostic in context.

The cascade becomes a *tutorial loop*. The runner explains, in
type-theoretic terms, exactly which subgoal the LLM failed to
discharge. That's a real interaction loop, not a binary filter.

---

## What needs to be in place

Three prerequisites, all currently open. Each is in `FUTURE.md`.

### 1. The proof goal must be expressible and tractable

`multnExact_soundForCE_first_install` is the proposition the LLM
would need to prove for the multn case. But its proof is
~100 lines of tactic. Asking an LLM to discover that from scratch
is too much.

The fix: provide a *high-level tactic* — call it
`attempt_ce_soundness` — that handles the standard structural
pattern (closure with `(if (num? op) <branch> (orig op args))`
shape, captured `orig` bound to the previous gate, the standard
fuel and validity lemmas). The LLM then only has to fill in the
*policy-specific* parts: what `<branch>` does, why it's CE-safe
for the operators it covers.

The goal: get the LLM's contribution down to ~10 lines per
proposal, not 100. Achievable; this is exactly the kind of
domain-specific tactic Lean is good at.

### 2. The elaboration path must be sandboxed

Today, `Elab.lean` runs `lake env lean --run` on a wrapper that
splices the LLM's output into a Lean source file. **This is not a
security boundary.** A model can emit `#eval ...`, top-level
declarations, side-effecting commands, anything — and they all
run during elaboration. The runner's verdict-parser sees the
*last line of stdout*, which the model can also influence.

For the proof-cascade to be a real proof-checker, this seam has
to be a proper sandbox. Three options, in order of isolation:

- **Black `Expr` parser** — LLM emits a string in a small Black-
  source notation; a Lean function in `Black.lean` parses it.
  Eliminates Lean elaboration-time effects entirely.
- **JSON AST** — LLM emits JSON for `Expr`; deserialize directly.
- **Sandboxed elaboration** — keep the current shape, but run the
  elaborator in a process with no network, no credentials,
  read-only repo, and a private temp dir.

The first two are the right long-term answers. The third is a
short-term mitigation. ("Hardening the proposal-to-admission
seam" item 7 in `FUTURE.md`.)

### 3. `BlackPolicy` must admit context

The current `Val → Val → Bool` can't reference the target name,
the heap, or the metaEnv. The proof obligation `CE old new`
*requires* knowing those — without the heap, you can't talk about
`OrigBoundIn`; without the target name, you can't restrict the
modification to the `base-apply` cell.

The fix (FUTURE.md / *Hardening the proposal-to-admission seam* /
item 3): extend `BlackPolicy` to take a `MutationCtx`:

```lean
structure MutationCtx where
  target  : String
  heap    : Heap
  env     : Env
  metaEnv : Env
  index   : Nat

abbrev BlackPolicy := MutationCtx → Val → Val → Bool
```

Once the policy can see context, `multnExactPolicy` can check
`target = "base-apply"` *and* the install-protocol facts *and*
delegate to a soundness checker that sees the same context. The
proof obligation is then well-formed against what the runtime
gate actually knows.

---

## The full picture

If items 1–3 land, the round shape becomes:

```
Round N:

  Runner state: heap, metaEnv, active policy,
                set of admitted proposals so far,
                published architectural floor (a Lean Prop)

  LLM input:
    - state summary + previously admitted proposals
    - the floor as a Lean goal (e.g. "prove CE base-apply <new>")
    - previous round's diagnostic if any (the unsolved goal,
      the type mismatch, etc.)

  LLM output:
    (modification : Expr, proof-script : tactic-block)

  Runner (in sandboxed elaborator):
    elaborate `modification` to an Expr value
    elaborate `proof-script` against the floor goal
    Lean kernel type-checks the proof

    if both succeed:
      admit, install via the policy gate, run witness program
    else:
      reject; pass the kernel's diagnostic into the next round's input
```

This is the architectural form for **LLM-driven program
transformation with verified correctness**. Three properties make
it research-grade:

- The LLM is untrusted. It can produce anything.
- The runner is untrusted to *judge*. It only runs the Lean kernel.
- The Lean kernel's correctness is the only TCB. Standard
  type-theoretic guarantees apply.

If any of those three properties is violated, the cascade
collapses back into "trust the LLM" or "trust the runner's
discipline." Today, the runner's discipline is in the TCB
(structural gate, splice-and-run elaboration). The proof-cascade's
goal is to move that discipline into the type system, where it
becomes machine-checkable.

---

## What this isn't

A few things explicitly out of scope:

- **Not a replacement for Black-level reflection.** The Black
  layer continues to do reflective `.set` over the meta-env. The
  proof-cascade governs *which mutations are admitted*; it does
  not change the underlying reflective architecture.
- **Not a discharge of every possible soundness obligation.** The
  cascade is parameterized by the published floor. If the floor is
  weak (single-call CE), so are the guarantees. The user picks
  the floor by changing one definition.
- **Not a model of the LLM's reasoning.** The LLM is a black box
  that produces (proposal, proof) pairs; the cascade only cares
  whether the kernel accepts the proof. How the LLM arrived at
  the proof is its own affair.
- **Not (yet) a complete pipeline.** It's an architectural target;
  items 1–3 above are real prerequisites, each of nontrivial size.

---

## Where this fits in the project

- The current cascade (`Bedrock` / `Elab` / `Runner`) is the
  *structural* form. It validates the propose-gate-witness shape
  but uses a `Bool` gate.
- `multnExact_soundForCE_first_install` is the *propositional
  target* — the kind of theorem the cascade would have the LLM
  prove for each admission.
- `FUTURE.md` enumerates the three prerequisites and the deeper
  items (multi-install, richer policy library, proof-carrying
  policies).

The current artifact is the substrate for the proof-cascade. The
verified policies are the things the LLM would be trying to
satisfy proofs against. The cascade architecture (propose →
elaborate → admit-or-reject) already has the right shape. What's
missing is items 1–3 to turn the structural gate into a proof
gate.

---

## Pointers

- `Runner.lean`, `Elab.lean`, `Bedrock.lean` — the current
  cascade implementation.
- `Policies.lean` — the policy library and the
  `multnExact_soundForCE_first_install` headline theorem (the
  shape of the target proof goal).
- `FUTURE.md` — *Hardening the proposal-to-admission seam* (the
  three prerequisites) and *LLM-cascade extensions* (the broader
  research direction).
- `PATH_A.md` — the framing-theorem story; relevant because the
  proof-cascade's soundness obligations compose `frame` (set-free
  framing) with the install-protocol theorem.

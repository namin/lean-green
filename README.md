# lean-green

A verified Black-faithful reflective interpreter in Lean 4, with an
LLM-driven proposer/gate cascade and the value-bisimulation
infrastructure needed to prove conservative-extension soundness for
governed reflective modifications.

See [`DESIGN.md`](DESIGN.md) for the full design.

## Three load-bearing properties

1. **Causal connection.** A `set!` against the meta-env's
   `base-apply` from inside `(em ...)` observably changes how the
   base level evaluates applications. The meta-level is data — not
   modeled by an indexed table, but by a heap cell whose mutation
   propagates to future dispatch.

2. **Parametric verified governance.** Modifications to meta-env
   bindings are gated by a current `BlackPolicy` drawn from a
   verified policy table. Soundness is parameterized over an
   architectural floor `P : Val → Val → Prop` — canonical instance
   is conservative extension. Switching policies is itself a
   reflective step (`installPolicy`).

3. **LLM-driven proposer.** A Bedrock-mediated cascade where Claude
   proposes Black-source modifications, which are elaborated and
   admitted (or refused) under the active policy. The kernel
   discipline is real: the LLM cannot bypass the gate, the gate
   cannot generate proposals.

## What's verified

Three layers:

- **Structural** (`Policies.lean`). `numGuardPolicy` admits exactly
  the recognized syntactic shape; `multnExactPolicy` admits exactly
  the strict multn pattern with delegating else-branch. Inversions of
  pattern-matching definitions, by case analysis.

- **Operational** (`Policies.lean`). The headline theorem
  `multnExact_soundForCE_first_install`: `multnExactPolicy` is sound
  for `ConservativeExt`. Side-conditions bundled into two load-
  bearing structures:

  ```
  theorem multnExact_soundForCE_first_install
      (h_admit : multnExactPolicy .builtinBaseApply new = true)
      (h_fuel  : fuel ≥ 2)
      (h_old   : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
                   = some (r, s'))
      (install : InstallFacts new s.heap)
      (wf      : RuntimeWF new metaEnv op operands s.heap) :
      ∃ fuel' s'' r',
        callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
        ValVis r r' s'.heap s''.heap
  ```

  - **`InstallFacts`** — install-time facts (`OrigBoundIn` +
    `NumQBoundIn` for the multn closure's cenv).
  - **`RuntimeWF`** — runtime validity invariants (`HeapValid`,
    `EnvValid metaEnv`, `EnvValid (cenvOf new)`, `ValValid op`,
    `ListValValid operands`); the runner naturally maintains them.

  The fuel bound is trivially satisfied at the call site
  (`Smoke.lean` runs at `fuel = 10000`). **Proved**, modulo the
  open `.set`-in-`frame` case below — the headline theorem only
  invokes `frame.applyDirect` on the post-install user-call (which
  is set-free in any sane runner program), so the open `.set` case
  doesn't bite the headline result in practice.

- **Infrastructure** (`Bisim.lean`). The framing theorem `frame` —
  parallel statements for `eval`, `evalList`, `applyVia`,
  `applyDirect`. Built on depth-indexed `ValVis_aux` / `EnvVis_aux`,
  `WFCtx` invariant bundle, `HeapExt` (same-side heap-
  monotonicity), `StateExt` (cross-side same-policy), `ListValVis`,
  `ValValid` / `HeapValid` / `EnvValid` validity machinery, plus
  `applyPrim_bisim` (per-prim bisim respect, ~600 LOC) and
  `alloc_chain_bisim` (foldl-induction for closure-call arg
  allocation, ~150 LOC). All cases of `eval`/`evalList`/`applyVia`/
  `applyDirect` are closed *except* the `.set` case of `frame.eval`,
  which remains an open `sorry` (see *Open work* below). The
  `.quote` case is closed by a runtime `closedValB` check on the
  quoted value, restricting `.quote` to closure-free values.

Value relation `ValVis` is syntax-based data refinement à la CakeML
(Kumar 2016 §3): two closures relate iff their bodies are equal and
their captured envs are pointwise related. The natural same-`Val`
framing is provably false in the presence of closures with captured
envs.

The cross-side `StateExt` is just **policy equality**. An earlier
heap-prefix component (`∃ extras, s_b.heap = s_a.heap ++ extras`)
was provably wrong as an output invariant — independent allocations
on the two sides break it. The cross-side heap relation is implicit
through `ValVis` / `EnvVis` on the relevant values, which take two
heaps without requiring a prefix relation.

## Status

**One `sorry` remains** — the `.set _ _` case of `frame.eval` in
`Bisim.lean`. The `.quote v` case of `frame.eval` and the
`multn_closure_body_unfolds` trace lemma are both closed.

### Concessions

Two concessions worth flagging up-front:

0. **The runner partially enforces the verified theorem's
   preconditions.** As of the runner-vs-theorem hardening
   (`FUTURE.md` / *Hardening the proposal-to-admission seam*
   items 1, 3, 6), the runtime gate *can* inspect the heap and
   target name: `BlackPolicy` is now `MutationCtx → Val → Val →
   Bool`. `multnExactPolicy` checks `target = "base-apply"`,
   `OrigBoundIn`, and `NumQBoundIn` at runtime, and the bridge
   lemma `multnExactPolicy_implies_InstallFacts` proves that
   admission discharges exactly the install-protocol facts the
   headline theorem requires. The TOCTOU `.set`-RHS-policy-
   downgrade attack is closed by freezing `s.policy` before the
   RHS evaluates. Adversarial smoke tests (scene 3 of `Smoke.lean`)
   exercise these end-to-end — shadowed-`orig`, wrong target,
   numGuard-shaped malicious all refused. **What remains:** the
   active *runner* policy in `Elab.lean` / `Runner.lean` is still
   hardcoded to `numGuardPolicy` (loose syntactic shape). Switching
   to `multnExactPolicy` is now mostly a config flip; see item 4
   of the hardening section in `FUTURE.md`. Until that flip lands,
   what *can* be enforced isn't yet what *is* enforced by the
   default runner — but the kernel-side proof and the runtime
   policy-side check are now aligned.

1. **`eval`'s `.quote v` is restricted to "closed" values.** `eval`
   checks `closedValB v` at the `.quote v` case and returns `none`
   if it fails. A closed value is one with no closure references
   (atoms and cons-trees of atoms). The framing case for `.quote`
   then closes via `closedValB_ValVis_aux`, since closed values
   self-bisimulate across any pair of heaps without heap-prefix
   relations. *Practical impact:* none. The only `.quote` use in
   this development is `.quote .nilV` in `Smoke.lean`.

### Open work — the `.set` case of `frame.eval`

The framing theorem cannot, in general, hold across reflective
`.set` for policies that admit *operationally* CE-extending
modifications without requiring *structural* (`ValVis`)
equivalence. Concretely: `multnExactPolicy` admits replacing
`.builtinBaseApply` (a tag constructor) with a `.closure` value
(a different constructor) — these are different `Val` constructors
and so not `ValVis_aux`-related by inversion. Closing this case
requires a real architectural choice, of three:

- **Restrict `frame`'s domain to set-free expressions** — cheap,
  lots of bookkeeping (~150 LOC of `SetFreeExpr` / `SetFreeVal` /
  `HeapSetFree` predicates threaded through ~20 `frame` cases).
  Was tried (and reverted: was over-engineered for what it bought).
- **Replace `HeapExt` with a `HeapEvolves` relation** — heap may
  grow *or* be updated at an existing index with a value related
  to the old one by a *policy-respecting-bisim* invariant. Add
  the policy-respecting-bisim hypothesis to `WFCtx`; prove
  `ValVis_aux_evolves` / `EnvVis_aux_evolves` lemmas. Cleaner,
  more infrastructure (~500 LOC). The hypothesis is satisfied by
  every policy in `verifiedTable`.
- **Replace `ValVis` with a step-indexed logical relation** —
  deepest fix; structural `body_a = body_b` requirement on
  closures becomes operational. Major rewrite of bisimulation
  infrastructure.

The headline theorem `multnExact_soundForCE_first_install` does
not depend on `.set`-in-`frame` being closed. Internally it
invokes `frame.applyDirect` on a post-install user-call, which
is set-free in any sane runner program — `.set` doesn't appear
in the trace `frame` actually walks. `multn_closure_body_unfolds`
likewise stays closed. The `sorry` lives in a case that none of
the current artifact's load-bearing claims walk through.

See `FUTURE.md` / *Generalizing the infrastructure* for the
design space if you want to close the case rather than route
around it.

## Layout

```
lean-green/
├── lakefile.lean
├── lean-toolchain                 — leanprover/lean4:v4.20.0
├── LeanBlack.lean                 — top-level imports
├── LeanBlack/
│   ├── Black.lean                 — Val, Expr, Env, Heap, RunState, eval, ...
│   ├── Bisim.lean                 — ValVis, EnvVis, WFCtx, HeapExt, framing theorems
│   ├── Policies.lean              — BlackPolicy, library, multnExact_soundForCE_first_install
│   ├── Bedrock.lean               — `aws bedrock-runtime invoke-model` wrapper
│   ├── Elab.lean                  — proposal elaboration via `lake env lean --run`
│   └── Runner.lean                — one-round cascade
├── Smoke.lean                     — `lake exe smoke`: un-governed and governed demos
├── BedrockSmoke.lean              — `lake exe bedrock-smoke`: connectivity check
├── RunnerMain.lean                — `lake exe runner [N]`: N rounds of LLM cascade
├── DESIGN.md                      — full design document
└── README.md                      — this file
```

## Prerequisites

- **Lean toolchain.** Pinned to `leanprover/lean4:v4.20.0` via
  `lean-toolchain`. With `elan` on PATH, the right toolchain is
  fetched automatically on first `lake build`.
- **AWS CLI** (only for the LLM cascade). `aws` on PATH, credentials
  in the standard chain (env vars or `~/.aws/credentials`), and
  Bedrock access for the configured model in the configured region.
  Defaults: model `us.anthropic.claude-sonnet-4-6`, region
  `us-east-1`.

## Build

```bash
lake build
```

## Ways to run it

Three executables are declared in `lakefile.lean`:

### `lake exe smoke`

Un-governed and governed demos. No external dependencies.

- *Un-governed* (default `acceptAllPolicy`): the multn pattern works
  via `set! base-apply` from inside `em`, *and* a malicious
  modification that overwrites `base-apply` with a constant-returning
  closure also admits — after which `(+ 1 2)` evaluates to `0`.
  Reflection without governance.
- *Governed* (`installPolicy idx_numGuard`): the same malicious
  modification is refused (returns `false`); `(+ 1 2)` still returns
  `3`; the multn pattern is admitted and `(2 3 4) ⇒ 24`.

The same mutation mechanism is gated by whichever policy is active.
Switching policies via `installPolicy` is itself an explicit
reflective step.

### `lake exe bedrock-smoke`

One-shot connectivity check against Bedrock. Sends a trivial prompt
and prints `OK: <text>` or exits non-zero on error. Requires the AWS
CLI and Bedrock credentials.

### `lake exe runner [N]`

Runs `N` rounds of the full LLM cascade (default `N = 3`). Each
round:

1. Prompts Claude (via Bedrock) for a Black-source modification as a
   Lean 4 `Expr`.
2. Elaborates the proposal by splicing it into a wrapper that
   installs it under the active policy and runs a witness program
   via `lake env lean --run`.
3. Records the verdict: `ADMITTED → <repr>` / `REJECTED` /
   `ELAB-ERROR`.

Admitted proposals are accumulated and shown to Claude in
subsequent rounds. A final summary reports admitted / rejected /
elab-error counts.

```bash
lake exe runner          # 3 rounds (default)
lake exe runner 10       # 10 rounds
```

## References

- [`DESIGN.md`](DESIGN.md) — full design, including the verification structure,
  the proof chain, refinements that emerged from the build, and
  remaining risks.
- [`docs/Kumar_2016_thesis.pdf`](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-879.html) — primary inspiration for the
  bisimulation infrastructure (Chapter 3, data refinement for
  closures, fuel-based divergence preservation).
- [`black/black.scm`](https://github.com/readevalprintlove/black/blob/master/black.scm) — Asai/Matsuoka/Yonezawa 1996 reference
  implementation that this Lean 4 development reimplements the core
  reflective architecture of.

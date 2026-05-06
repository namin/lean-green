# lean-green

A verified Black-faithful reflective interpreter in Lean 4, with an
LLM-driven proposer/gate cascade and the value-bisimulation
infrastructure needed to prove conservative-extension soundness for
governed reflective modifications.

See `DESIGN.md` for the full design.

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
  for `ConservativeExt` under eleven hypotheses (`OrigBoundIn`,
  `NumQBoundIn`, `HeapValid`, `EnvValid metaEnv`,
  `EnvValid (cenvOf new)`, `ValValid op`, `ListValValid operands`,
  `HeapSetFree s.heap`, `SetFreeVal op`, `SetFreeListVal operands`,
  `fuel ≥ 2`). The first two are install-time facts; the next five
  are runtime invariants the runner naturally maintains; the three
  Path-A side-conditions (`HeapSetFree` / `SetFreeVal` / `SetFreeListVal`)
  reflect the operationally honest framing-domain restriction
  discussed under *Concessions* below; the fuel bound is trivially satisfied
  at the call site (`Smoke.lean` runs at `fuel = 10000`). **Fully
  proved.** The trace lemma `multn_closure_body_unfolds` and the
  composition with `frame.applyDirect` are both closed.

- **Infrastructure** (`Bisim.lean`). The framing theorem `frame` —
  parallel statements for `eval`, `evalList`, `applyVia`,
  `applyDirect`. Built on depth-indexed `ValVis_aux` / `EnvVis_aux`,
  `WFCtx` invariant bundle (now including `HeapSetFree` on both
  sides), `HeapExt` (same-side heap-monotonicity),
  `StateExt` (cross-side same-policy), `ListValVis`,
  `ValValid` / `HeapValid` / `EnvValid` validity machinery,
  `SetFreeExpr` / `SetFreeVal` / `HeapSetFree` set-free
  domain-restriction predicates, plus `applyPrim_bisim` (per-prim
  bisim respect, ~600 LOC), `alloc_chain_bisim` (foldl-induction
  for closure-call arg allocation, ~150 LOC), and
  `applyPrim_SetFreeVal` (closure-of-prims under set-free args).
  **Fully closed.** `frame.eval`'s `.set` case is discharged by
  contradiction from `SetFreeExpr`; `.quote` is discharged by a
  runtime `closedValB` check on the quoted value. The *Concessions*
  section below explains why the set-free domain restriction is the
  principled answer for this language rather than a limitation.

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

**No `sorry`s remain.** All three previously open items in `frame`
and `Policies.lean` are closed.

### Concessions made to close them

Two of the three closures changed the development's surface area.

1. **`eval`'s `.quote v` is now restricted to "closed" values.**
   `eval` checks `closedValB v` at the `.quote v` case and returns
   `none` if it fails. A closed value is one with no closure
   references (atoms and cons-trees of atoms). The framing case for
   `.quote` then closes via `closedValB_ValVis_aux`, since closed
   values self-bisimulate across any pair of heaps without heap
   prefix relations.

   *Practical impact:* none. The only `.quote` use in this
   development is `.quote .nilV` in `Smoke.lean`. Programs that
   need to quote a closure-bearing value would now fail at runtime
   rather than silently produce a structurally-unsound value
   reference.

2. **`frame`'s domain is restricted to set-free expressions.** The
   four mutual statements of `frame` now take `SetFreeExpr exp` /
   `SetFreeListExpr exps` / `SetFreeVal op` / `SetFreeListVal args`
   hypotheses, and `WFCtx` carries `HeapSetFree` on both sides.
   The `.set _ _` case of `frame.eval` discharges by contradiction
   from `SetFreeExpr (.set _ _) = False`.

   *Why this is principled, not a regression:* a *structural*
   framing theorem across reflective `.set` is **provably false**
   for the policies that make reflective mutation interesting.
   `multnExactPolicy` admits replacing `.builtinBaseApply` (a tag
   constructor) with a `.closure` value (a different constructor) —
   these are operationally equivalent (CE-extending) but structurally
   non-`ValVis`-related by inversion. The very policies that make
   reflective mutation meaningful cannot satisfy a "policy admits
   only `ValVis`-related transitions" hypothesis. The principled
   factoring is: framing covers the non-reflective sublanguage, and
   reflective `.set` steps are covered separately by install-
   protocol theorems like `multnExact_soundForCE_first_install`
   (which uses framing on the *post-install user-call*, where no
   `.set` appears). `DESIGN.md`'s *Refinements / `.set` and Path A*
   subsection walks through the argument in detail.

   *Practical impact on the headline theorem:*
   `multnExact_soundForCE_first_install` now takes three
   additional hypotheses — `HeapSetFree s.heap`, `SetFreeVal op`,
   `SetFreeListVal operands` — that any sensible runner trivially
   maintains. The runner only ever calls user ops (prims or
   set-free closures) on heap-resident values that came from
   `.lam` / atomic literals.

### What's closed and how

- **`.quote v`** — runtime `closedValB` gate in `eval` +
  `closedValB_ValVis_aux` / `closedValB_ValValid` /
  `closedValB_SetFreeVal` reflexivity lemmas.
- **`.set`** — Path A (set-free domain restriction). ~150 LOC of
  new predicates, preservation lemmas, and threading through ~20
  `frame` cases. `WFCtx` extended with two `HeapSetFree` fields;
  every `WFCtx` constructor updated. See `DESIGN.md` /
  *Refinements / `.set` and Path A* for the full argument.
- **`multn_closure_body_unfolds`** — explicit step-by-step
  reduction. The deterministic eval-trace through the multn
  closure body unfolds to `applyDirect fuel ptable op operands`
  at the alloc'd state via a chain of `simp only` calls keyed
  on the four heap+env lookup facts. No infrastructure friction
  (the `(s.heap ++ [v]).length` vs `s.heap.length + 1` issue
  noted in earlier comments was avoidable with the right
  reduction order).

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

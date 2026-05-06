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
  documented in `FINDINGS.md`; the fuel bound is trivially satisfied
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
  runtime `closedValB` check on the quoted value. See `FINDINGS.md`
  for why the set-free domain restriction is the principled answer
  for this language rather than a limitation.

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

**No sorries remain.** All three previously open items are closed:

- **`.quote v`** in `frame` — closed by introducing a `closedValB`
  runtime check in `eval`'s `.quote` case, restricting quoted Vals
  to closure-free values, with a matching `closedValB_ValVis_aux`
  reflexivity lemma. Existing demos (`Smoke.lean` only quotes
  `.nilV`) are unaffected.
- **`.set`** in `frame` — closed by Path A: `frame` is restricted
  to set-free expressions via `SetFreeExpr` / `SetFreeVal` /
  `HeapSetFree` predicates threaded through the four mutual
  statements. The `.set _ _` case discharges by contradiction from
  `SetFreeExpr (.set _ _) = False`. `FINDINGS.md` documents why
  this domain restriction is the principled answer (a structural
  framing theorem across reflective `.set` is provably false for
  the policies — like `multnExactPolicy` — that make reflective
  mutation interesting).
- **`multn_closure_body_unfolds`** — closed by an explicit
  step-by-step reduction of `callAsBaseApply` on the multn closure
  through `applyDirect`'s closure-case foldl-alloc, then through
  `eval` of the `.ifte` cond and else-branches.

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

- `DESIGN.md` — full design, including the verification structure,
  the proof chain, refinements that emerged from the build, and
  remaining risks.
- `docs/Kumar_2016_thesis.pdf` — primary inspiration for the
  bisimulation infrastructure (Chapter 3, data refinement for
  closures, fuel-based divergence preservation).
- `black/black.scm` — Asai/Matsuoka/Yonezawa 1996 reference
  implementation that this Lean 4 development reimplements the core
  reflective architecture of.

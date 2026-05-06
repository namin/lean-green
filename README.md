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
  for `ConservativeExt` under eight hypotheses (`OrigBoundIn`,
  `NumQBoundIn`, `HeapValid`, `EnvValid metaEnv`,
  `EnvValid (cenvOf new)`, `ValValid op`, `ListValValid operands`,
  `fuel ≥ 2`). The first two are install-time facts; the next five
  are runtime invariants the runner naturally maintains; the fuel
  bound is trivially satisfied at the call site (`Smoke.lean` runs
  at `fuel = 10000`). Proved conditional on the inner trace through
  the closure body in `multnExact_CE_nonnum_case` (the structural
  setup is done; the remaining ~200 LOC mechanical eval-trace is
  open).

- **Infrastructure** (`Bisim.lean`). The framing theorem `frame` —
  parallel statements for `eval`, `evalList`, `applyVia`,
  `applyDirect`. Built on depth-indexed `ValVis_aux` / `EnvVis_aux`,
  `WFCtx` invariant bundle, `HeapExt` (same-side heap-monotonicity),
  `StateExt` (cross-side same-policy), `ListValVis`,
  `ValValid` / `HeapValid` / `EnvValid` validity machinery, plus
  `applyPrim_bisim` (per-prim bisim respect, ~600 LOC) and
  `alloc_chain_bisim` (foldl-induction for closure-call arg
  allocation, ~150 LOC). **Closed for all eval/evalList/applyVia
  cases and all `applyDirect` constructor cases (closure, prim,
  builtinBaseApply); two `eval` cases remain — see *Open work*
  below.**

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

## Open work

Three items remain `sorry`'d, all architectural rather than
mechanical:

- **`.quote v`** in `frame` — needs a `ClosedVal v` predicate
  restricting quoted Vals to those without closure references, or
  `ValValid v` on both heaps as an additional hypothesis.
- **`.set`** in `frame` — the meta-mutation policy gate breaks
  under bisimulation since `s.policy` can return different verdicts
  on `ValVis`-related-but-unequal inputs. Needs a "policy is
  bisimulation-respecting" hypothesis added to `WFCtx` (the policies
  in `verifiedTable` actually satisfy it, but encoding this is a new
  design decision).
- **Inner trace of `multnExact_CE_nonnum_case`** — structural
  prerequisites are established (closure shape, `orig`/`num?`
  indices, `applyDirect fuel op operands` from `h_old`). The
  remaining gap is a mechanical eval-trace through the closure
  body that ends in a single `frame.applyDirect` application.

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

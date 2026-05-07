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
   admitted (or refused) under the active runtime policy. The
   *runtime kernel* discipline is real: at the operational layer,
   admitted proposals are gated by the verified policy and the LLM
   cannot bypass that gate. The *elaboration cascade* is
   demonstration scaffolding, not a security boundary — see
   *Known limitations* below.

## What's verified

Three layers:

- **Structural** (`Policies.lean`). `numGuardPolicy` admits any
  closure whose body begins `(if (num? <var>) ... ...)` (loose,
  intentionally not CE-sound — see *Policy table* below).
  `multnExactPolicy` admits any closure whose body has the shape
  `(if (num? op) <numeric-branch> (orig op args))` *with the
  delegating else-branch fixed* and `cenv` binding `orig` to the
  current `base-apply` and `num?` to `.prim "num?"`. The numeric
  branch is structurally a wildcard at the policy level; CE
  soundness in the headline theorem follows because the numeric
  branch never executes for non-numeric operators (it's the only
  path through `applyDirect builtinBaseApply` for `.num` ops, which
  is `none`).

- **Operational** (`Policies.lean`). The headline theorem
  `multnExact_soundForCE_first_install`: `multnExactPolicy` is sound
  for `ConservativeExt`. Side-conditions bundled into two load-
  bearing structures:

  Informal sketch (the actual signature in `Policies.lean` adds
  policy-table soundness, deep-validity, and shift-respect side
  conditions):

  ```
  theorem multnExact_soundForCE_first_install
      (h_admit : multnExactPolicy ctx .builtinBaseApply new = true)
      (h_fuel  : fuel ≥ 2)
      (hresp_pt   : PolicyTableRespectsBisim ptable)
      (hresp_init : PolicyRespectsBisim s.policy)
      (h_old   : callAsBaseApply fuel ptable .builtinBaseApply op operands metaEnv s
                   = some (r, s'))
      (install : InstallFacts .builtinBaseApply new s.heap)
      (wf      : RuntimeWF new metaEnv op operands s.heap)
      -- Deep-validity (runtime-built heap maintains alloc-only growth):
      (h_heap_deep : HeapDeep s.heap)
      (h_op_deep : ValDeep op s.heap)
      (h_operands_deep : ListValDeep operands s.heap)
      (h_meta_deep : EnvDeep metaEnv s.heap)
      -- Shift-respect (every `BlackPolicy` here is structural):
      (h_pt_shift  : PolicyTableRespectsShift s.heap.length _ ptable)
      (h_pol_shift : PolicyRespectsShift s.heap.length _ s.policy) :
      ∃ fuel' s'' r',
        callAsBaseApply fuel' ptable new op operands metaEnv s = some (r', s'') ∧
        ValVis_weak r r' s'.heap s''.heap ∧
        s'.policy = s''.policy ∧
        HeapValid s''.heap ∧
        s.heap.length ≤ s''.heap.length
  ```

  - **`InstallFacts`** — install-time facts (`OrigBoundIn` +
    `NumQBoundIn` for the multn closure's cenv).
  - **`RuntimeWF`** — runtime validity invariants (`HeapValid`,
    `EnvValid metaEnv`, `EnvValid (cenvOf new)`, `ValValid op`,
    `ListValValid operands`); the runner naturally maintains them.
  - **Deep validity** — `HeapDeep`/`ValDeep`/`EnvDeep`/`ListValDeep`
    are the *deep* validity predicates (every embedded index, not
    just looked-up bindings, is in-bounds). `runtime_invariants_initial`
    discharges them for the runner's startup state.
  - **Shift-respect** — `PolicyRespectsShift` is the shift analog of
    `PolicyRespectsBisim`; `verifiedTable_respects_shift` and
    `acceptAllPolicy_respects_shift` discharge the relevant cases.
  - The conclusion is `ValVis_weak` (not `ValVis`) — see
    [`WAND.md`](WAND.md), *Why the headline CE statement is `_weak`*.

  The fuel bound is trivially satisfied at the call site
  (`Smoke.lean` runs at `fuel = 10000`). **Proved**, sorry-free.

- **Infrastructure** (`Bisim.lean`). The framing theorem `frame` —
  parallel statements for `eval`, `evalList`, `applyVia`,
  `applyDirect`. Built on depth-indexed `ValVis_aux` / `EnvVis_aux`,
  `WFCtx` invariant bundle, `HeapExt` (same-side heap-
  monotonicity via `HeapEvolution`), `StateExt` (cross-side same-
  policy), `ListValVis`, `ValValid` / `HeapValid` / `EnvValid`
  validity machinery, `PolicyRespectsBisim` (cross-side gate
  symmetry on bisim-related inputs), plus `applyPrim_bisim`
  (per-prim bisim respect, ~600 LOC), `alloc_chain_bisim` and
  `allocStep_chain_aligned` (foldl-induction for closure-call arg
  allocation, ~200 LOC), and `ValVis_aux_update` /
  `EnvVis_aux_update` (mutual depth induction for in-place cell
  update preserving bisim, ~250 LOC). **All cases of
  `eval`/`evalList`/`applyVia`/`applyDirect` are closed**, including
  the `.set` case of `frame.eval`. The `.quote` case is closed by a
  runtime `closedValB` check on the quoted value, restricting
  `.quote` to closure-free values.

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

**Zero sorries across `Bisim.lean`, `Black.lean`, and
`Policies.lean`.** Every theorem builds clean.

The proof has two parallel paths:

- **Cross-side `frame`** (the original): joint induction with
  `WFCtx`'s `env_eq` / `heap_len_eq` invariants, `HeapEvolution`,
  and the `ValVis_aux_update` / `EnvVis_aux_update` self-update
  depth induction. Closes the cross-side `.set` case.
- **Functional shift** (`shift_respect`): the prefix-extension
  becomes a syntactic `shift_idx` / `shift_val` / `shift_env` /
  `shift_heap` operation; `eval`/`evalList`/`applyVia`/
  `applyDirect` all *commute* with shift. Closes
  `applyDirect_heap_extend_via_shift` without needing a
  cross-side `heap_len_eq` invariant — exactly the obstacle that
  made the historical asymmetric `(s, s_alloc)` setup fail.

`applyDirect_heap_extend_weak` is a thin wrapper over
`applyDirect_heap_extend_via_shift`. The `.set` case in
`shift_respect` closes via `PolicyRespectsShift` (the shift-flavored
analog of `PolicyRespectsBisim`), which `policy_shift_preserved`
threads through the joint induction. `verifiedTable_respects_shift`
proves all three verified policies (`rejectAll`, `numGuardPolicy`,
`multnExactPolicy`) are shift-respecting; `acceptAllPolicy_respects_shift`
covers the default initial policy. `initState_deep` and
`runtime_invariants_initial` establish `HeapDeep` / `EnvDeep` /
`PolicyTableRespectsShift` / `PolicyRespectsShift` for the runtime
starting state.

### Policy table

`verifiedTable = [rejectAll, numGuardPolicy, multnExactPolicy]`.

| Policy              | CE-sound?                              | Purpose                                |
|---------------------|----------------------------------------|----------------------------------------|
| `rejectAll`         | yes (vacuously — admits nothing)       | baseline                               |
| `numGuardPolicy`    | **no** — else-branch unconstrained     | loose demo / adversarial contrast      |
| `multnExactPolicy`  | yes (first install, conditional)       | the headline operational theorem       |

"Verified table" means each entry is verified to be
`PolicyRespectsBisim` and `PolicyRespectsShift`, *not* that each
entry is CE-sound. CE soundness is per-policy and stated by the
relevant theorem (`multnExact_soundForCE_first_install` for
`multnExactPolicy`).

### Known limitations

- **First-install only.** `multnExact_soundForCE_first_install`
  covers the first install (where `oldVal = .builtinBaseApply`).
  Multi-install (subsequent multn replacements) requires a
  parametric variant; the bridge lemma
  `multnExactPolicy_implies_InstallFacts` is already
  `oldVal`-parametric, but the headline soundness theorem isn't
  yet wrapped to use it.
- **`CE_weak`, not `CE`.** The headline operational theorem
  concludes `ValVis_weak`, the relaxed bisim that drops Lean-equal-
  `cenv` requirements on closures. See [`WAND.md`](WAND.md), *Why
  the headline CE statement is `_weak`*.
- **`multnExactPolicy`'s numeric branch is unconstrained at the
  policy level.** Any closure body of the form
  `(if (num? op) <anything> (orig op args))` is admitted (provided
  cenv binds `orig` and `num?` correctly). The headline theorem
  goes through because the only `applyDirect builtinBaseApply` path
  for non-`.num` operators is the `else` branch. Strengthening the
  numeric branch (e.g., to a fixed `mul-list`-based body, or via
  a `NoSetNoInstallNoEm` syntactic predicate) is future work.
- **LLM elaboration is not sandboxed.** The proposer-elaborator
  runs Lean against model-generated text via `lake env lean --run`;
  malicious top-level Lean commands take effect at elaboration
  time, before any runtime gate runs. This is demonstration
  scaffolding, not a security boundary — see
  [`LLM_PROOF_CASCADE.md`](LLM_PROOF_CASCADE.md).
- **No machine-checked top-level "runner is sound" theorem.** The
  chain `multnExact_soundForCE_first_install → ... → runner` is
  proved up to the operational theorem; the runner's metaprogram
  is not itself verified, and there is no top-level theorem
  stating "running the runner under the verified table preserves
  CE." All public theorems are about the operational kernel.

**`LeanBlack/Wand.lean`** carries the value-level existential
defeat of Wand 1998 — non-syntactically-equal expressions (a
β-redex and its contractum) whose top-level evaluation under any
policy table agrees — together with three concrete contextual
instances. The full contextual W1 (universal over arbitrary
syntactic contexts), W2, and W3 are tracked in `WAND.md`.

### Concessions

Two concessions worth flagging up-front:

0. **The runner enforces the verified theorem's preconditions.**
   As of the runner-vs-theorem hardening (`FUTURE.md` /
   *Hardening the proposal-to-admission seam* items 1, 2, 3, 4, 6):

   - `BlackPolicy` is `MutationCtx → Val → Val → Bool` — the gate
     sees target name, heap, env, metaEnv, and index.
   - `multnExactPolicy` is `oldVal`-parametric: it checks
     `target = "base-apply"`, the strict multn shape, and that
     the captured `orig` cell holds *the current `base-apply`*
     (whatever it is — `.builtinBaseApply` for first install, the
     previous multn closure for subsequent installs). The
     mutual `Val.beq`/`Expr.beq`/`Env.beq` machinery in
     `Black.lean` and the lemma `val_beq_eq` lift the runtime
     `Bool` admission to the propositional equality the bridge
     lemma needs.
   - The bridge lemma `multnExactPolicy_implies_InstallFacts`
     proves that runtime admission discharges
     `InstallFacts oldVal new ctx.heap` for *any* `oldVal`,
     making the runtime gate multi-install ready.
   - The `.set` clause freezes `s.policy` before evaluating the
     RHS, closing the TOCTOU `installPolicy`-mid-RHS downgrade
     attack.
   - `Elab.lean`'s wrapper enforces a syntactic restriction:
     proposals must be exactly `.lam ["op", "args"] body`. RHS
     preludes, nested `.em`, and `.set`-ful sequences are
     rejected at the elaboration layer (defense-in-depth).
   - The active runner policy in `Elab.lean` / `Runner.lean` is
     `multnExactPolicy` (`idx_multnExact = 2`).
   - Adversarial smoke tests (scene 3 of `Smoke.lean`, 8 cases)
     exercise all of this end-to-end — shadowed-`orig`, wrong
     target, `numGuard`-shaped malicious, TOCTOU downgrade,
     multi-install all behave as expected.

   The runner's "ADMITTED" verdict now means: the runtime gate
   verified the install-protocol facts that the headline
   soundness theorem requires. Kernel and runtime are aligned.

   *What's left:* the elaboration path (`Elab.lean` /
   `lake env lean --run`) is still not a security boundary —
   the LLM can emit Lean elaboration-time effects that aren't
   caught by the syntactic check. See `GOTCHAS.md` #17 and
   `FUTURE.md` / *Hardening seam* / item 7.

1. **`eval`'s `.quote v` is restricted to "closed" values.** `eval`
   checks `closedValB v` at the `.quote v` case and returns `none`
   if it fails. A closed value is one with no closure references
   (atoms and cons-trees of atoms). The framing case for `.quote`
   then closes via `closedValB_ValVis_aux`, since closed values
   self-bisimulate across any pair of heaps without heap-prefix
   relations. *Practical impact:* none. The only `.quote` use in
   this development is `.quote .nilV` in `Smoke.lean`.

### `.set` framing — closed (historical note)

The framing theorem holds across reflective `.set` for policies
that admit *operationally* CE-extending modifications without
requiring *structural* (`ValVis`) equivalence. Concretely:
`multnExactPolicy` admits replacing `.builtinBaseApply` (a tag
constructor) with a `.closure` value (a different constructor) —
these are different `Val` constructors and so not `ValVis_aux`-
related by inversion. The trick is that the bisim is *cross-side*:
`HeapEvolution s_a s_b s_a' s_b'` records that env-bisim and val-
bisim are preserved cross-side across the step, not that same-side
old/new are bisim-related (which is impossible for multn).

The architecture that closed this case:

- **Cross-side `HeapEvolution`** replacing `HeapExt s_a s_a' ∧
  HeapExt s_b s_b'`. Captures cross-side env- and val-bisim
  preservation across an in-place update.
- **`PolicyRespectsBisim`** invariant on `WFCtx.policy_resp`. The
  active policy gives the same admit/reject decision on bisim-
  related arguments — this lets the `.set` case argue both sides
  decide the same way.
- **`env_eq` and `heap_len_eq`** invariants on `WFCtx`. Ensure
  `env.lookup x` produces the same `idx` cross-side, so
  `isMetaMutation` agrees and the heap update targets the same
  cell on both sides.
- **`ValVis_aux_update` / `EnvVis_aux_update`** mutual depth
  induction (with bounded `< n` precondition) for in-place cell
  updates. The bound enables a self-update universal-depth lemma
  via depth-induction with a strengthened IH.

Total: ~700 LOC of new proved infrastructure in `Bisim.lean`.

The `multnExact_CE_nonnum_case` historical asymmetric-framing
issue is resolved via the shift-based prefix-extension path
described in the *Status* section above.
`applyDirect_heap_extend_weak` now takes additional Deep-validity
and `PolicyRespectsShift` preconditions, propagated to
`multnExact_CE_nonnum_case` and `multnExact_soundForCE_first_install`;
`runtime_invariants_initial` discharges them for the initial
runner state.

## Layout

```
lean-green/
├── lakefile.lean
├── lean-toolchain                 — leanprover/lean4:v4.20.0
├── LeanBlack.lean                 — top-level imports
├── LeanBlack/
│   ├── Black.lean                 — Val, Expr, Env, Heap, RunState, eval, ...
│   ├── Bisim.lean                 — ValVis, EnvVis, WFCtx, HeapEvolution, framing theorems
│   ├── Policies.lean              — BlackPolicy, library, multnExact_soundForCE_first_install
│   ├── Wand.lean                  — value-level existential defeat of Wand 1998 (W1)
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

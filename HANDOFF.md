# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
The first three recursion clauses are checked uniformly in all finite
alphabets: `coloringLLT_column`, `coloringLLT_concat`, and
`coloringLLT_unicellular`. `coloringLLT_firstBounce` now proves the first
single-bounce clause; the second remains open.

The finite path/graph/coloring model is independent of any recurrence.
`EExpansion` and `evalElementary` interpret formal elementary expressions
separately. No general symmetric-functions library or circular work is needed.

Latest source checkpoints, all pushed on private `main`:

- `f7bb5b4`: general unicellular identity and color-swap primitives.
- `b92dbb5`: restricted swap sum, prefix scanners, valid local path swaps.
- `36cc80a`: second-bounce successor and audited coloring-involution plans.

Full/default build (1409 jobs), all 101 public axiom checks, source guards,
line-length checks, `git diff --check`, and immutable-reference checks pass.
Only standard Lean axioms occur. Logs:

- `/lake-cache/ai-projects/build/VerticalStripLLT/first-bounce-full-build.log`
- `/lake-cache/ai-projects/build/VerticalStripLLT/first-bounce-axioms.log`

## Live work and next action

Issue #4 tracks the two single-bounce coloring identities:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/4.
Issues #1–3 are completed. Read `docs/BOUNCE_PLAN.md` before implementing the
bounce geometry; it records independently audited word/endpoint hypotheses
and the direct coloring involutions, including equality boundary cases.

Aristotle's first-bounce proof is complete, ported into four modules by Luna,
independently audited by Terra, and locally verified by primary.
Second-bounce project `6bc089d7-87cb-4db2-b199-f4c4b4d05ee3`, task
`eccb0402-2bde-4fbe-8eaf-19847e0f41ca`, is confirmed `QUEUED` (2026-09-25).
It must derive the graph geometry and full second identity from word
hypotheses; its request includes nineteen checked source modules.
Observe this same task; do not restart merely because an observer expires.
All remote provenance, inputs, outputs, and environment details are in
`docs/ARISTOTLE.md`.

Claude Sonnet completed the read-only recursion audit (native exec session
`56969` exited successfully). Primary checked its claims against the manuscript;
see `docs/RECURSION_PLAN.md` for accepted conclusions and corrections.
Prompt/output: `/lake-cache/ai-projects/requests/VerticalStripLLT/recursion-audit/`.
No nested Claude process remains active.

Next: port and locally verify the second-bounce candidate when returned.
Meanwhile the next bounded word task is converse column classification using
`Step.endpointFrom_counts` and `SchroderPath.northCount_eq_eastCount`.
Generalized bounce and exact decrease certificates follow; see
`docs/RECURSION_PLAN.md` for the audited decomposition.

## Ownership and build discipline

Primary `/root` owns strategy, integration, and the sole project build slot.
Both Luna port assignments are complete and ownership has returned to primary:
`BounceScanners.lean`, `FirstBounceGraph.lean`, `BounceWeight.lean`,
`FirstBounce.lean`, `WordCounts.lean`, and `PolynomialCancellation.lean`.
The full build and axiom checkpoint passed; no local build is active.
Terra independently audited the completed first-bounce candidate and confirmed
source fidelity, unchanged definitions, and derived graph hypotheses.

The user explicitly requests modular code, sparse/batched compilation, and
parallel bounded delegation to Aristotle and smaller Claude/Luna/Terra models.
Primary still performs the authoritative local builds. Check no global Lean/
Lake process is active before each invocation; use only `lake-workspace`,
reduced priority, and an appropriate compiler timeout. Never use plain Lake,
edit generated cache files, or change dependencies to fit a remote candidate.

## Checked supporting modules

`ColumnBase.lean` proves the general initial condition. `ColoringConcat.lean`
proves graph decomposition, weight factorization, and coloring multiplicativity.
`Unicellular.lean` proves marked-edge scanner/finset identities and the general
unicellular polynomial relation.

`ColoringSwap.lean` gives the swap involution and monomial preservation.
`SwapSum.lean` proves admissibility/ascent/weight and restricted-sum statements
under explicit graph symmetry hypotheses. `FirstBounceGraph.lean` proves those graph hypotheses for the first bounce;
`FirstBounce.lean` gives the resulting full path-based coloring identity.

`PrefixScanners.lean` gives unconditional arbitrary-prefix append laws.
`BouncePath.lean` proves the two valid local swaps; `SecondBouncePath.lean`
composes them into the second successor. These helpers are not bounce identities.
The source map is in `docs/FORMALIZATION.md`; earlier declaration inventories
and checkpoint history are in `docs/archive/handoff-through-bounce-helpers.md`.

## Environment and remaining theorem work

Initialization commits `830cc6b`, `130f7e8` and reviewed architecture `81b4885`
are preserved. Reference files remain unchanged from `130f7e8`.
Lean is `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected; never run `lake update`.
No local `.lake/packages` or `.lake/build` exists. Dependencies/builds live
under `/lake-cache/ai-projects`.

SSH push authentication is unavailable. Use invocation-local HTTPS rewriting
and `gh auth git-credential`, preserving the configured remote. Lean MCP defaults
to RealRooted: use explicit-root read-only searches and local wrapper checks.
Aristotle uses an isolated Lean/Mathlib 4.28 snapshot; local 4.34 verification
is authoritative. No local toolchain or account changes are permitted.

After single-bounce proofs: generalized bounce reduction; decrease lemmas for
`(size, east count, first-east height)`; recurrence uniqueness; recursive
invariant with named coloring bridge; independent orientation/HRV expression
and its recurrence; ordinary expansion, shifted positivity, degree/stability.
The manuscript's `F_ne=1` typo is resolved as `e₁`. Cancellation of q−1 over
integral coefficient rings must be justified explicitly.

Previous goal turn: verified progress. This continuation has further checked
proof progress and confirmed live auxiliary jobs; no blocking audit applies.

# VerticalStripLLT handoff

## Current state

- Ordinary LLT expansion remains the active goal; it is not yet proved.
- General initial condition is proved: `coloringLLT_column` gives
  `G_(n d^k e) = e_(k+1)` for every k and every finite alphabet.
- Path edges have increasing endpoints, strict and normal edges are disjoint,
  and raw scanners satisfy endpoint bounds, translation, and append laws.
  `SchroderPath.concat` constructs the valid concatenation of two paths.
- `coloringLLT_concat` proves coloring multiplicativity for arbitrary valid
  paths and every finite alphabet. Its completed Aristotle candidate was
  ported by Luna and verified locally without changing the pinned toolchain.
- Earlier empty/singleton and size-two unicellular theorems remain checked.
- Finite colorings split across a vertex concatenation, and independent sums
  factor. Both local resolutions of a diagonal step preserve path validity;
  the unchanged normal/strict scanners are proved equal.
- The elementary-coloring bijection proof came from a live Aristotle candidate,
  was ported by Luna, and passed local Lean 4.34 builds and axiom checks.
- Full/default build and all 51 declarations in `Verification.lean` pass;
  only standard Lean axioms appear. Source guards and reference-integrity checks pass.
- Primary `/root` owns strategy, integration, all current source files, and
  the sole project build slot. No delegated source edit or local build is active.

## Immediate next action

Pursue the general unicellular relation in issue
https://github.com/PerAlexandersson/VerticalStripLLT/issues/3.

Aristotle project `7cac7db7-a2d1-4c27-8522-9b43c7690ed8`, task
`2496607b-8e35-455c-9ee7-7a60c6ef4618`, is `IN_PROGRESS` on that exact
statement (latest observation 4 percent, editing `Request.lean`). The request
includes the checked path resolution, marked endpoint, and pointwise weight
lemmas. Inspect this handle; do not restart on an observation timeout.
Provenance and isolated environment details are in `docs/ARISTOTLE.md`.
Luna should port the candidate; primary remains sole local builder.

Remaining proof outline: characterize changed normal/strict edge sets by
inserting `markedDiagonalEdge`; freshness follows from strict/normal
disjointness. Apply `coloringWeight_unicellular_of_edges` and sum over all
colorings. The source map records the exact assumptions. The coloring
polynomial remains independently defined, never defined by the recurrence.

All latest Luna assignments are integrated and released. `path_invariants`
authored `MarkedDiagonal.lean` and independently audited the concatenation
and marked-edge statements, finding no scope issues. `column_paths` authored
`UnicellularWeight.lean` and ported Aristotle's `ColoringConcat.lean`. Primary
fixed final API/transparency details and ran every build; both Luna workers
remain build-free and own no files until explicitly reassigned.

## New declarations and source correspondence

All declarations below are under `VerticalStripLLT`.

- `PathInvariants.lean`: `Step.normalFrom_lower_bound`,
  `strictFrom_lower_bound`, `normalFrom_lt`, `strictFrom_lt_of_valid`,
  `normalFrom_strictFrom_disjoint`; `SchroderPath.normalEdges_lt`,
  `strictEdges_lt`, `normalEdges_disjoint_strictEdges`.
- `PathBounds.lean`: `Step.validFrom_bounds`, `normalFrom_upper_bound`,
  `strictFrom_upper_bound`.
- `Column.lean`: `SchroderPath.column`, `column_normalEdges`,
  `column_strict_mem_iff`, `column_strictEdges`, `column_ascentCount`,
  `admissible_column_iff`.
- `ElementaryColorings.lean`: `increasingColoringSum`,
  `increasingColoringSum_eq_esymm`, including degree zero and empty alphabet.
- `ColumnBase.lean`: `coloringLLT_column`,
  `coloringLLT_column_eq_evalElementary`. This is Theorem `recursion` (i) and
  Proposition `coloringProperties` (i), manuscript lines 823–828, 2306–2321.
- `Concat.lean`: `Step.validFrom_translate`, `validFrom_append_of_valid`,
  `normalFrom_append_of_valid`, `strictFrom_append_of_valid`,
  `normalFrom_translate`, `strictFrom_translate`; `SchroderPath.concat`,
  `concat_steps`.
- `ColoringSplit.lean`: `coloringSplitEquiv`, forward/inverse restriction
  simp lemmas, `sum_colorings_split`, `sum_colorings_split_mul`.
- `UnicellularPath.lean`: `Step.validFrom_resolve`, `normalFrom_resolve`,
  `strictFrom_resolve`; `SchroderPath.resolveNorthEast`, `resolveEastNorth`,
  and their step-list simp lemmas. The general polynomial relation is open.

- `ColoringConcat.lean`: eight scanner block identities, `leftPairEmb`,
  `rightPairEmb`, `disjoint_left_right_maps`, `concat_normalEdges`,
  `concat_strictEdges`, `admissible_concat_append`, `ascentCount_concat_append`,
  `coloringWeight_concat_append`, `coloringLLT_concat`. This proves Proposition
  `coloringProperties` (ii), manuscript lines 2323–2339.
- `MarkedDiagonal.lean`: `Step.endpointFrom`, `validFrom_suffix`,
  `strictFrom_marked`, `markedDiagonal_bounds`; `SchroderPath.markedDiagonalEdge`
  and `markedDiagonalEdge_mem`.
- `UnicellularWeight.lean`: `coloringWeight_unicellular_of_edges`, with explicit
  edge-set hypotheses; the general path polynomial identity remains open.

## Ownership and checks

Luna `path_invariants` authored `PathInvariants.lean`, `PathBounds.lean`,
ported Aristotle's draft into `ElementaryColorings.lean`, and proved the
column bridge in `ColumnBase.lean`. Luna `column_paths` authored `Column.lean`
and `Concat.lean`. Both returned their source and ran no builds. Primary
integrated their work, fixed final normalization/API details, and compiled it.
Neither Luna worker currently owns a file; record ownership before reassignment.

Focused checks passed for all three new modules, then the full/default build
(1369 jobs) and `lake-workspace env lean Verification.lean` passed. Logs:

- `/lake-cache/ai-projects/build/VerticalStripLLT/multiplicativity-build.log`
- `/lake-cache/ai-projects/build/VerticalStripLLT/multiplicativity-axioms.log`

No `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` in production
source. Lean source is at most 100 columns. `git diff --check` passes and the
reference snapshot is unchanged from `130f7e8`. No local `.lake/packages` or
`.lake/build`. Only primary invokes `lake-workspace`, with reduced priority,
a 20-minute compiler bound, and a process guard that aborts if Lean/Lake is active.
An axiom run was correctly deferred while RealRooted built; it ran after that
process exited. Do not infer build-slot ownership from an old lock or status note.

## Repository checkpoints and environment

- Initialization preserved: `830cc6b`, `130f7e8`.
- Reviewed architecture, committed before scaffolding: `81b4885`.
- First verified slice: `cab97ea9b353ff62772e0e154323964013d2704e`.
- General graph invariants and column characterization: `4d0fddd`, pushed.
- General elementary base case and raw concatenation laws: `961bc99`, pushed.
  Milestone issue #1 is complete; issue #2 is now proved locally as well.
- Coloring sum factorization and unicellular path resolutions: `6d72a1b`,
  pushed after full build, 39 axiom checks, and source/reference guards.
- Private repository, branch `main`. No branch, remote, or account changes.
- Lean `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Wrapper package-directory warning is expected; never respond with `lake update`.
- SSH push authentication is unavailable; use the existing invocation-local
  HTTPS rewrite and `gh auth git-credential` without changing the remote.
- Lean MCP defaults to RealRooted: use explicit-root read-only search and local
  wrapper checks. AXLE is available. Aristotle CLI works; it advertises Lean
  4.28, so all candidates must be verified against the local pinned environment.

## Remaining main-theorem work

General unicellular and bounce identities; bounce
reduction; lexicographic decrease lemmas for `(size, east count, first-east
height)`; recurrence uniqueness; recursive elementary invariant and coloring
bridge; independent orientation/HRV construction and its recurrence; ordinary
expansion and shifted positivity; weighted degree and alphabet specialization.
The full theorem must compare independently defined semantic objects.

The manuscript's `F_ne=1` sentence is a typo: we use `e₁`. Division by `q−1`
requires justified cancellation in our integral coefficient model. References
under `references/alexandersson-sulzgruber-2022/` are immutable. No circular,
cumulant, or flip-component work has begun. See `docs/FORMALIZATION.md` for the
complete source map and `docs/archive/handoff-first-slice.md` for initial history.

Previous goal turn classification: progress. This continuation also makes
verified proof progress; no blocking audit applies. The overall goal stays active.

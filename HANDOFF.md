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
- `coloringLLT_unicellular` proves the general relation for every valid
  diagonal word and finite alphabet. The first three recursion clauses are
  now checked; the two single-bounce clauses remain open.
- Finite colorings split across a vertex concatenation, and independent sums
  factor. Both local resolutions of a diagonal step preserve path validity;
  the unchanged normal/strict scanners are proved equal.
- The elementary-coloring bijection proof came from a live Aristotle candidate,
  was ported by Luna, and passed local Lean 4.34 builds and axiom checks.
- Full/default build and all 74 declarations in `Verification.lean` pass;
  only standard Lean axioms appear. Source guards and reference-integrity checks pass.
- Primary `/root` owns strategy, integration, all current source files, and
  the sole project build slot. Current bounded assignments are below.

## Immediate next action

Pursue the single-bounce coloring relations using the audited decomposition
in `docs/BOUNCE_PLAN.md`. The general unicellular theorem has passed the local
batch build and axiom audit; issue #3 is closed. The bounce milestone is issue
https://github.com/PerAlexandersson/VerticalStripLLT/issues/4.

Aristotle project `30bbdfee-3932-4a5d-84a7-bd0d29bf82e2`, task
`80bb72e2-fde2-415c-af6e-ffef30b9da06`, is newly submitted (initially `QUEUED`)
for the full first-bounce identity with the exact word/return/gap hypotheses
in `docs/BOUNCE_PLAN.md`. Its snapshot includes fourteen checked modules.
The earlier swap-sum task completed and is integrated; do not resume it.
Use the new exact handle and verify any candidate locally. Full provenance
and immutable request locations are in `docs/ARISTOTLE.md`.

Luna `path_invariants` authored `BouncePath.lean`; Luna `column_paths`
authored `PrefixScanners.lean` and ported `SwapSum.lean` from Aristotle.
All three modules are locally checked; source ownership has returned to
primary. Terra independently checked the exact first-bounce word certificate
and identified the faithful background `R ++ [east,east,north] ++ W`.

User steering: keep modules separate, batch local compilation, and delegate
bounded independent tasks in parallel to Aristotle and smaller models.
Primary remains sole local builder. No delegated source edits are active.
The immediate independent local task is the second-bounce successor, using
the two checked swaps and preservation of prefix endpoints. Record ownership
before assigning it. No full bounce identity or recursive/orientation bridge
is claimed.

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
  and their step-list simp lemmas.

- `ColoringConcat.lean`: eight scanner block identities, `leftPairEmb`,
  `rightPairEmb`, `disjoint_left_right_maps`, `concat_normalEdges`,
  `concat_strictEdges`, `admissible_concat_append`, `ascentCount_concat_append`,
  `coloringWeight_concat_append`, `coloringLLT_concat`. This proves Proposition
  `coloringProperties` (ii), manuscript lines 2323–2339.
- `MarkedDiagonal.lean`: `Step.endpointFrom`, `validFrom_suffix`,
  `strictFrom_marked`, `markedDiagonal_bounds`; `SchroderPath.markedDiagonalEdge`
  and `markedDiagonalEdge_mem`.
- `UnicellularWeight.lean`: `coloringWeight_unicellular_of_edges`, with explicit
  edge-set hypotheses.

- `Unicellular.lean`: raw marked-edge scanner identities, the four resolved
  edge-set identities, marked-edge freshness, `coloringLLT_unicellular`.
  This proves Proposition `coloringProperties` (iii), lines 2341–2352.
- `ColoringSwap.lean`: `swapColors`, evaluation/involution lemmas,
  `prod_X_swapColors`, `swapColorEquiv`. No admissibility/ascent preservation
  without graph hypotheses is claimed.

- `PrefixScanners.lean`: `Step.endpointFrom_append`, `normalFrom_append`,
  `strictFrom_append`, all without prefix-validity hypotheses.
- `BouncePath.lean`: `Step.validFrom_diagonalNorth_swap`,
  `validFrom_diagonalEast_swap`; valid-path constructors `swapDiagonalNorth`,
  `swapDiagonalEast` and their step-list simp lemmas.
- `SwapSum.lean`: `swapVertexPair`, `card_filter_swapColors`,
  `admissible_swapColors_iff`, `ascentCount_eq_swapColors_add_one`,
  `coloringWeight_eq_C_X_mul_swapColors`, `coloringLLT_swap_sum`.
  Explicit graph symmetry hypotheses remain to be proved for each bounce use.

## Ownership and checks

Luna `path_invariants` authored `PathInvariants.lean`, `PathBounds.lean`,
ported Aristotle's draft into `ElementaryColorings.lean`, and proved the
column bridge in `ColumnBase.lean`. Luna `column_paths` authored `Column.lean`
and `Concat.lean`. Both returned their source and ran no builds. Primary
integrated their work, fixed final normalization/API details, and compiled it.
Neither Luna worker currently owns a file; record ownership before reassignment.

The three returned modules were checked in a focused batch; after the final
Lean 4.34 coercion/rewrite fixes, the full/default build (1374 jobs) and all
74 axiom checks passed. Logs:

- `/lake-cache/ai-projects/build/VerticalStripLLT/swap-sum-build.log`
- `/lake-cache/ai-projects/build/VerticalStripLLT/swap-sum-axioms.log`

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
- Coloring multiplicativity and unicellular helpers: `156aef3`, pushed;
  full build and 51 public axiom checks pass. Issue #2 is closed.
- General unicellular relation and swap primitives: `f7bb5b4`, pushed;
  full build and 62 public axiom checks pass. Issue #3 is closed; issue #4
  tracks the remaining two single-bounce recursion clauses.
- Private repository, branch `main`. No branch, remote, or account changes.
- Lean `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Wrapper package-directory warning is expected; never respond with `lake update`.
- SSH push authentication is unavailable; use the existing invocation-local
  HTTPS rewrite and `gh auth git-credential` without changing the remote.
- Lean MCP defaults to RealRooted: use explicit-root read-only search and local
  wrapper checks. AXLE is available. Aristotle CLI works; it advertises Lean
  4.28, so all candidates must be verified against the local pinned environment.

## Remaining main-theorem work

Single-bounce identities; bounce reduction; lexicographic decrease lemmas for `(size, east count, first-east
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

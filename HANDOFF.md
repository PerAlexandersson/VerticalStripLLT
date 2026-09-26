# VerticalStripLLT handoff

## Active continuation: circular coloring–HRV equality

The full circular theorem remains open. The checked outer induction has one
explicit input, `InteriorNDInductionStep`. Ordinary expansion, first-contact
interior overlap, direct/root-alias/separated ND, and complete NN/DN are proved.
Strict cycles make both actual models vanish; overlapping offset contact tracks
alone do not form a cycle. No flip work is active.

The active route constructs a smaller diagram by reversing the columns of the
merged strict component. Both its validity and strict doubled-area decrease
were verified at `e2f3479`. Its actual strict graph and positive integer lifts
are proved to be transported by the reversal (`e88d287`). Exterior normal-edge
transport, sink order and actual residual coloring/HRV equality are now verified.
Restoring forced factors and applying the lower-area induction remain. Exact formulas are in
`docs/proofs/CIRCULAR_COLUMN_REVERSAL.md`.

The user's one-bounce strategy remains the surrounding reduction. Do not assume
termination of every arbitrary DD/DN/R1 rewrite sequence. The earlier ordinary
paired-child route uses a shorter-prefix induction for its raised child, not
smaller area; see `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.

## Current checkpoint: actual residual coloring and HRV transport

`InteriorResidualTransport` proves:

- `liftStep_exterior_reversal_iff`: every exterior normal-edge selection has
  exactly its transported integer lifted graph.
- `orientSum_exterior_reversal`: the actual restricted HRV sums agree,
  including cyclic selections.
- `coloringLLT_exterior_reversal`: actual residual coloring sums agree for
  every finite alphabet.

The residual graphs retain all strict edges and remove exactly those normal
edges whose two endpoints are in the merged component. These are consequences
of the concrete target, not extra transport or semantic hypotheses.

Supporting modules separate the geometry:

- `InteriorBoundaryAvoidance.boundary_avoids_column_interior`: outside heads
  cannot have boundaries inside a column; the component sink uses the eligible
  root's skipped boundary value.
- `InteriorLiftIntervals`: lifted column containment and order comparisons
  against outside points; no global monotonicity of reversal is asserted.
- `InteriorReversalSource`: the nonstrict source's exact boundary formula and
  the unchanged comparisons against exterior tails.
- `InteriorExteriorBoundary.boundaryNaturalLift_reversal_iff`: actual exterior
  integer edge intervals in both directions, including winding.
- `InteriorExteriorPairs`: actual finite strict, natural and normal pair
  correspondence.
- `InteriorReversalSinkOrder.reversalLift_order_sinks`: order on all integer
  sinks, for arbitrary selected edge sets.
- `InteriorResidualPairs`: exact residual pair sets and permutation equalities.

Focused builds passed, ending with 1519 jobs for residual transport. Full default
build passed (1904 jobs); all 2015 inventory declarations use only standard
axioms. Source guards, 100-column limit and whitespace checks pass. Independent
Astra audits approved both geometry and actual polynomial semantics.

Luna supplied the boundary-singleton, sink-order and residual-set candidates;
Terra supplied the exterior fixed-point candidate. Primary completed full
interval, avoidance, source, exterior-edge and residual transport proofs and
corrected the candidate APIs. Only primary invoked local builds.

Previous verified checkpoint `e88d287`: strict integer-lift transport, full build
1896 jobs and 1982 standard-only axiom declarations. Earlier source/target and
ordinary checkpoints remain in the archive and Git.

## Ownership and verification

All delegate edit lanes are released. Primary owns strategy, integration,
remote requests and the sole local build slot. No build-slot transfer occurred.
Use only `lake-workspace`, check for other Lean/Lake processes before each
invocation, and keep generated outputs outside the checkout. Lean MCP still
targets RealRooted, so it is not used for implicit project checks.

External logs under `/lake-cache/ai-projects/requests/VerticalStripLLT/`:
`interior-exterior-geometry-build.log`, `interior-residual-transport-build.log`,
`interior-residual-transport-full-build.log`, and
`interior-residual-transport-axioms.log`.

Earlier detailed checkpoints and ownership history are retained in
`docs/archive/circular-interior-checkpoints-through-e2f3479.md` and Git.
Initialization commits `830cc6b`, `130f7e8` and immutable manuscript references
remain preserved. No Overleaf edits in this continuation.

## Aristotle provenance

The existing full interior request finished **COMPLETE_WITH_ERRORS**:
project `65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, task
`a430cbfd-eb82-4070-b9c2-002ae875cb53`. Its final source retains exactly one
placeholder, the full `expansion_of_nd_interior_overlap` target. Nothing from
this return was imported. The only new proved wrapper repeats the existing
first-contact result. Its exploratory rank calculations are not proof of a
mathematical obstruction.

The archive and inspected files are retained externally under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-interior-with-chain-base/`:
`result.tar.gz`, `returned-Request.lean`, `returned-ARISTOTLE_SUMMARY.md`, and
`returned-REMAINING_ISSUE.md`. Final source SHA256:
`680e6d017cb24fe780ec3356e220d4d3bb67670986355a7f693cbbe042b0f2e9`.
Input source was `5266faa`, before the column-reversal construction. No live
remote proof task remains; do not restart an observer for this completed task.

The successful chain-singleton request was already integrated at `5266faa`.
Older request and compatibility provenance is retained in `docs/ARISTOTLE.md`
and the archived handoff. Local Lean4.34 verification remains authoritative.

## Next proof obligations

Restore the internal normal-edge factors for D and its actual reversal target.
For D use `K.vertexEmbedding`; for Q use this embedding followed by
`K.reversalPerm`. The strict chain orders all component vertices, so every
internal normal edge is either a forced ascent or a forced descent. Apply the
existing coloring/orientation forced-set and descent-set lemmas, and identify
the remaining normal pairs with `Diagram.exteriorNormalPairs`.

Both factorization counts must count the same normal-edge sets within each
model; no comparison between the source and target counts is required.
The checked residual coloring equality and HRV equality identify the common
remaining expressions. Apply the outer IH to Q using
`reversalTarget_doubledArea_lt`, cancel its nonzero (1+q) coefficient factor,
and restore D's factor. This must discharge the unchanged
`InteriorNDInductionStep`, not a strengthened variant.

Then instantiate the checked outer induction and transfer the already-proved
HRV coefficient positivity/weighted degree to actual coloring polynomials,
for every finite alphabet. The full circular theorem is not yet proved.

If further remote proof search is useful, supply the updated verified prefix
and isolate this factorization/cancellation step. The completed old task did
not receive any of the column-reversal construction or transport modules.

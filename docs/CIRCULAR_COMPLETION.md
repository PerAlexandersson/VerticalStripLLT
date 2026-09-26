# Circular HRV expansion completion audit

The full aggregate circular HRV formula is proved for every circular
Dyck/Motzkin diagram and every finite alphabet, including the empty alphabet.
The coloring polynomial and integer-cover HRV expression are independently
defined. No recurrence certificate, saturation, acyclicity, no-wrap premise,
or assumed semantic bridge occurs in the final statement.

## Public statements

All names below are in `VerticalStripLLT.Circular`, in
[`Circular/Expansion.lean`](../VerticalStripLLT/Circular/Expansion.lean).

- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion` identifies the
  coloring-defined LLT after q→q+1 with the independent elementary expression.
- `coloringLLT_shifted_eq_orientation_sum` exposes the formula with weights
  q raised to the number of ascending normal edges and elementary monomials
  indexed by highest-reachable-vertex fiber sizes.
- `coloringLLT_shifted_e_positive` supplies one elementary expression for all
  alphabet sizes, nonnegative integer coefficients at every q degree, and
  weighted homogeneity of degree n, assigning weight k to e_k.

`Diagram.specializeLast_coloringLLT` separately establishes compatibility with
setting the last alphabet variable to zero. We represent the symmetric-function
identity by this uniform finite-degree family; no general symmetric-functions
library is needed.

## Source correspondence

The current author draft is
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/main.tex`, SHA256
`287b5017072d50505f8fa0849c0ecefc52aac6536bb881015ab9cbe1c8611ce0`.
The target is `thm:circular-e-expansion` (line 1500 in this snapshot).

| Manuscript object | Lean representation and scope |
| --- | --- |
| Circular area sequence and decoration (lines 255 onward) | `CircularArea`, `Edge`, `Diagram`: n≥1, 0≤a_i<n, cyclic area inequality, arbitrary subset of permitted strict corners. |
| Coloring LLT | `Diagram.coloringLLT`: finite coloring sum with actual strict inequalities and normal-edge ascent weights. |
| Admissible orientations (lines 515–645) | `Orientation D`: ascending normal-edge selections whose union with strict edges is acyclic. Strictly cyclic diagrams remain allowed inputs to the theorem and contribute zero. |
| Highest reachable vertex | Greatest reachable integer on the universal cover, then residue; not the greatest finite vertex label. |
| Elementary factor | Product of e_k over HRV fiber sizes, equivalent to the partition-indexed elementary product by commutativity. |
| Formula after q→q+1 | `coloringLLT_shifted_eq_orientation_sum`, for every alphabet size. |

The corrected Lean proof uses half-square area and component reversal.
It does not certify every assertion of the older manuscript proof outline.
Updating that exposition to follow the checked argument is a separate writing
step. No Overleaf source was changed in this completion checkpoint, and the
committed ordinary-paper reference files remain immutable.

## Proof dependencies and termination

We use `doubledArea = 2 * sum area - strict.card` and strict rank for the
outer induction. Strict cycles vanish in both actual models. Complete bounce
search, neutral termination and the NN/DN/direct/separated/root-alias ND
relations reduce all but the interior-overlap case.

For that final case, the merged strict component has a concrete column
reversal giving a valid diagram Q with strictly smaller doubled area.
The periodic integer reversal transports strict edges and exterior normal
edges, preserves the required order of sinks, and identifies the actual
residual coloring and HRV sums. Global monotonicity of reversal is not used.

`ComponentFactorization` removes internal normal edges: forward edges along
the strict chain supply a factor (1+q)^F, and backward edges supply no ascent.
Both models use the same count F within each diagram. The counts for D and Q
need not agree. The polynomial factor is nonzero even for the empty alphabet,
so each full bridge is equivalent to its residual bridge. Applying the smaller
Q induction hypothesis transfers the bridge back to D.

The exact final interfaces are:

- `Diagram.expansion_iff_component_residual`;
- `Diagram.InteriorMergedComponent.expansion_of_reversalTarget`;
- `Diagram.expansion_of_nd_interior_overlap`;
- `interiorNDInductionStep`;
- `Diagram.expansion_of_interior_nd_step`, instantiated in `Circular.Expansion`.

The original interior induction interface is discharged unchanged. No general
projected multibounce relation or claim that every arbitrary rewrite sequence
terminates is required.

## Verification and provenance

The focused `Circular.Expansion` build passed (1772 jobs), followed by the
full default build (1908 jobs). All 2037 axiom-inventory declarations were
reported in exact order and use only `propext`, `Classical.choice`, and
`Quot.sound`. Source guards and whitespace/line-width checks pass. Logs are
recorded in [HANDOFF](../HANDOFF.md).
The inventory includes all 22 public declarations in the four final modules.
All local builds are serialized and run by primary using `lake-workspace`.

An independent Astra audit checked the manuscript scope, actual polynomial
semantics, factor cancellation, and the final hypotheses. Luna supplied the
component strict-path candidate and bounded documentation cleanup; Terra
reviewed the scalar APIs. Primary corrected, integrated and verified the code.
Aristotle supplied earlier isolated candidates; its last unfinished interior
return was not imported. See [the ledger](ARISTOTLE.md).

The two initialization commits remain ancestors, and the ordinary references
are unchanged. Earlier geometric checkpoints are preserved in Git and the
archived handoff.

## Separate open claims

The flip-component HRV identity remains unproved. E-positivity of the total
sum does not imply positivity of each component. The existing component
interfaces and exact target are retained in [CIRCULAR_FLIPS](CIRCULAR_FLIPS.md);
a complete proof should not be presumed. Weak/strict omega translation is a
separate representation bridge. Neither is a premise of the aggregate result.

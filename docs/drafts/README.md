# Draft and proof correspondence

The [ordinary component section](ORDINARY_COMPONENT_DIAGRAM_PROOF.md) develops
initial-vertex inheritance and right-endpoint attachment in detail. Its opening
states the component theorem, and its final section summarizes the established
component-recursion argument. The prerequisite local diagram lemmas and the
smaller-component corrections still need to be incorporated for a self-contained
paper. The mathematical source is the
[assembled proof](../proofs/COMPONENT_DIAGRAM_COMPLETION.md).

The independent Lean formalization is unfinished. The draft does not claim
otherwise; compiler status and source correspondence belong here and in the
[formalization plan](../COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), outside the
manuscript prose.

| Draft construction | Lean correspondence | Current scope |
| --- | --- | --- |
| Restrict after deleting zero | `initialVertex_anchor_restrict`, `induced_allCorners_initialVertex` | Checked |
| Make the selected core connected | `CornerFamily.exists_reachable_connected_initialVertex_core` | Checked actual crossing-slide paths |
| Keep initial extras fixed along a core path | `initialVertex_lift_reachable`, `initialVertex_reachable_of_same_initial_row` | Checked under smaller-core uniqueness |
| Figure 1: exact crossing-slide endpoint | `initialVertex_row_of_exchange`, `initialVertex_restrict_of_exchange` | Checked exact selected-edge identities |
| Choose the missing-edge witness and connect neighboring extra sets | `CornerFamily.exists_initialVertex_adjacent`, `initialVertex_reachable_of_erase_initial_row` | Checked under the stated removability/core-uniqueness hypotheses |
| Connect all feasible extra sets | `initialVertex_connected_core_anchors` | Checked actual assembly under the stated core hypotheses |
| Initial-vertex inheritance for common-cover states | `commonCover_connected_of_initialVertex_core` | Checked preparation, sector paths and reversed target preparation |
| Global common-cover uniqueness | P6 global induction | Unfinished |
| Endpoint-marked K and E | `markedK`, `markedE`, `markedK_diamond`, `markedE_diamond` | Existing checked semantics; see plan for the P2 interfaces |
| Figure 2: attachment and fibre merger | [Claude issue #8](https://github.com/PerAlexandersson/VerticalStripLLT/issues/8) | Detailed written proof; new Lean task |
| Whole-component corrections and marked recurrences | P7–P8 | Unfinished |
| First-drop coverage and final expansion | P9–P10 | Unfinished |

The final draft must also include the circular aggregate e-expansion. Its
checked proof uses half-square area, strict rank and reversal of the merged
strict component in the interior-overlap case. Start from
[the circular completion map](../CIRCULAR_COMPLETION.md) and inspect the actual
`Circular/Expansion.lean` dependencies before writing that section. Retain the
integer-cover HRV definition for circular diagrams. The ordinary component
section uses the ordinary greatest reachable vertex and the diagram proof
above. The combined manuscript is not yet assembled.

The SVG figures are editable vector sources. Their PNG previews live in the
external request cache, and both figures have been visually inspected. The
cell figure follows the diagonal-label and selected-cell convention of the
paper with Robin; its retained arrows indicate corner covers at the two
displayed endpoints.

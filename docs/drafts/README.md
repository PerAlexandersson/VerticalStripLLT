# Draft and proof correspondence

The [circular section](CIRCULAR_E_EXPANSION.md) gives the integer-cover
definition, aggregate expansion, local reductions, terminal-contact reduction,
interior column reversal and the area/rank induction. Its reversal figure is
an editable SVG, rendered and visually inspected. Local boundary checks and
DD-contact elimination are still compressed; the combined manuscript remains
to be assembled. The existing external circular-first manuscript was consulted
read-only; this draft explicitly separates terminal contact from interior
overlap to match the checked Lean decomposition.

The [ordinary component section](ORDINARY_COMPONENT_DIAGRAM_PROOF.md) now
includes the local diamond proof, absent-corner deletion, weak-block reordering,
alternating corner deletion, envelope normalization, and the full NN/DN layer
calculation with explicit selected-edge counts. It also develops
initial-vertex inheritance and right-endpoint attachment in detail. Its opening
states the component theorem, and its final section summarizes the established
component-recursion argument. Preparation, restored-exterior crossing slides, the complete and two-chain
bases, last-clique inheritance, and the chain-quotient path lemma still need
their detailed manuscript proofs. The final first-drop/prefix induction is
still summarized. The section is therefore not yet a self-contained paper. The mathematical source is the
[assembled proof](../proofs/COMPONENT_DIAGRAM_COMPLETION.md).

The independent Lean formalization is unfinished. The draft does not claim
otherwise; compiler status and source correspondence belong here and in the
[formalization plan](../COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), outside the
manuscript prose.

| Draft construction | Lean correspondence | Current scope |
| --- | --- | --- |
| Figure 1: diamond as a restricted sum | `diamond_hrv_maps`, `markedK_diamond`, `markedE_diamond` | Checked with arbitrary exterior; no cover hypothesis |
| Three smaller corrections and envelope | P7 | Detailed written proof; Lean unfinished |
| Figure 3: NN/DN layer sums and component isolation | P8 | Explicit size accounting in draft; Lean unfinished |
| Restrict after deleting zero | `initialVertex_anchor_restrict`, `induced_allCorners_initialVertex` | Checked |
| Make the selected core connected | `CornerFamily.exists_reachable_connected_initialVertex_core` | Checked actual crossing-slide paths |
| Keep initial extras fixed along a core path | `initialVertex_lift_reachable`, `initialVertex_reachable_of_same_initial_row` | Checked under smaller-core uniqueness |
| Figure 2: exact crossing-slide endpoint | `initialVertex_row_of_exchange`, `initialVertex_restrict_of_exchange` | Checked exact selected-edge identities |
| Choose the missing-edge witness and connect neighboring extra sets | `CornerFamily.exists_initialVertex_adjacent`, `initialVertex_reachable_of_erase_initial_row` | Checked under the stated removability/core-uniqueness hypotheses |
| Connect all feasible extra sets | `initialVertex_connected_core_anchors` | Checked actual assembly under the stated core hypotheses |
| Initial-vertex inheritance for common-cover states | `commonCover_connected_of_initialVertex_core` | Checked preparation, sector paths and reversed target preparation |
| Preserve chain count and discharge matching-edge removability | `CornerFamily.initialVertex_fixedTerminal_card`, `commonCover_connected_of_initialVertex_short` | Checked under short-edge and three-chain hypotheses, leaving smaller-core uniqueness |
| Preserve short edges in the canonical last-clique core | `lastClique_induced_short_naturalEdges` | Checked; reversed first-clique induction still needs assembly |
| At most two corner chains | `CornerFamily.commonCover_connected_of_terminal_card_le_two` | Checked cardinality wrapper for the two-terminal path theorem |
| Global common-cover uniqueness | P6 global induction | Unfinished |
| Endpoint-marked K and E | `markedK`, `markedE`, `markedK_diamond`, `markedE_diamond` | Existing checked semantics; see plan for the P2 interfaces |
| Figure 4: attachment and fibre merger | `IsRightAttachment.flipComponent_glue`, `hrv_glue_left`, `hrv_glue_right`, `attach_transfer` | Checked at `26b2d97`: whole product components, marked K/E transfer and measure decrease |
| Whole-component corrections and marked recurrences | P7–P8 | Unfinished |
| First-drop coverage and final expansion | P9–P10 | Unfinished |

The circular source map supplements [the completion audit](../CIRCULAR_COMPLETION.md):

| Draft construction | Related Lean | Scope |
| --- | --- | --- |
| Circular expansion theorem | `Circular/Expansion.lean`, `coloringLLT_shifted_eq_orientation_sum` | Checked aggregate theorem |
| Four selected triangles | `Circular/HRVTriangle.lean`, `tri_local_identity` | Integer-cover HRV identity |
| Terminal-contact reduction | `Circular/AliasRecurrences.lean`, `Diagram.exists_nd_alias_reduction`; `AliasReductionForced.lean`, `card_B`, `card_C` | Common factor `1+q`, doubled-area decrease six |
| Interior column reversal | `Circular/InteriorReversalReduction.lean`, `Diagram.expansion_of_nd_interior_overlap` | Strict interior intersection; terminal contact treated separately |
| Internal-edge factor cancellation | `Circular/ComponentFactorization.lean`, `Diagram.expansion_iff_component_residual` | Different source/target exponents allowed |
| Area and rank induction | `Circular/GeometricArea.lean`, `Diagram.doubledArea`; `NeutralTransport.lean`, `Diagram.strictRank` | Draft `J` is exactly the sum of proper-ancestor count times strict-edge length |

The ordinary section uses greatest reachable vertices in the ordinary order.
The circular section uses greatest reachable integers followed by reduction
modulo the period. Its theorem is aggregate; the ordinary section proves the
component refinement by the diagram route.

The [diagram macros and usage guide](tex/README.md) implement the user's
restricted-sum convention. A diagram specifies selected/absent/optional/strict
edges, forbidden natural pairs, cover conditions, total-size layers and endpoint
colors. Gray/white cells distinguish unweighted and normal-edge-weighted sums.
The two-page `diagram-examples.tex` preview and the diamond and NN/DN figures
compile without warnings or box overflows and were visually inspected.

The diamond and layer SVGs are generated from their small `.tex` sources using
`llt-diagrams.sty`; edit those sources rather than their generated font paths.
The other SVG figures are editable vector sources. Their PNG previews live in the
external request cache, and both figures have been visually inspected. The
cell figure follows the diagonal-label and selected-cell convention of the
paper with Robin; its retained arrows indicate corner covers at the two
displayed endpoints.

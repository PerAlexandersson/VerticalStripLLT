# Draft and proof correspondence

## Reader's route

The paper has two parts, as requested by the user:

1. **Circular elementary expansion by diagrams.** Define the integer-cover
   HRV statistic, prove the corner and bounce relations in both models, then
   handle intersecting paths by terminal reduction and column reversal.
2. **Component expansions by diagrams.** Reuse the corner and NN/DN diagrams
   on whole edge layers. Preparation and actual restored flip paths isolate
   a component; endpoint attachment closes the ordinary induction. The finite
   companion then reduces each circular component to the same signed sum of
   unions of ordinary components.

The second part ends with [LLT cumulants](CUMULANTS.md): set-partition
cancellation retains connected selections, which are unions of whole flip
components. The final corollary applies the component theorem to them.
This deduction is written and reviewed mathematically, but is not part of
the Lean formalization. The author information is restored from the earlier
Alexandersson--Dai draft in `tex/manuscript-authors.tex`; the closing
[AI statement](AI_STATEMENT.md) records assistance and that scope distinction.

The aggregate theorem alone is not the component proof. Its local identities
are reused with marked colors and fixed selected-edge counts. The circular
companion is stated explicitly; we do not assert that every circular bounce
or reversal preserves a single component.


The [introduction](INTRODUCTION.md) presents the two expansion theorems and
their diagram proofs, and compares the LLT and chromatic coloring sums.
The ordinary plethystic identity, common Dyck-path relations and circular
limitation are checked against AS22, Lemma 6.17, Corollary 6.18 and Section 6.8.
The four shifted recurrences (corner, NN, DN, ND) appear together in
`prop:fourRecurrences`, with the circular ND separation hypothesis explicit.
`references.bib` records the source. Paper-cache entry **496** contains
arXiv **2004.09198v2**, its exact-version PDF, source archive and extracted
text; PDF SHA256 is
`bb56b53c5efc3c2cd5bdbc243d354db84143eaf43adcbe22879e0fbeae826513`.
The introduction also compares Hwang's heap components with the present
LLT components, citing his Proposition 3.7, Theorems 3.8 and 4.19,
Conjecture 3.10, and Section 5.3. Paper-cache entry **497** contains
arXiv **2208.09857v2**. Entry **498**, arXiv **2112.12676v2**, supplies
Dołęga--Kowalski's connected expansion (Theorem 3.8) and ordinary cumulant
elementary expansion (Theorem 3.17). All three exact-version PDFs and source
archives are cached. The existing earlier draft was read only; its weak
coloring notation has been translated to the present strict `K` convention,
so the new cumulant argument requires no involution.
The [circular section](CIRCULAR_E_EXPANSION.md) gives the integer-cover
definition, aggregate expansion, local reductions, terminal-contact reduction,
interior column reversal and the area/rank induction. Its reversal figure is
now generated from native TeX, rendered and visually inspected. DD-contact elimination now
has explicit child and closing row tables, eligibility and contact-count
arguments, and a weighted-sum figure. The boundary-swap coloring proof,
cyclic cases of the HRV diamond, seven separated-ND identities and
column-reversal boundary checks are now expanded. The combined manuscript is generated from these canonical sections. The existing external circular-first manuscript was consulted
read-only; this draft explicitly separates terminal contact from interior
overlap to match the checked Lean decomposition.

The [ordinary component section](ORDINARY_COMPONENT_DIAGRAM_PROOF.md) now
includes the local diamond proof, absent-corner deletion, weak-block reordering,
alternating corner deletion, envelope normalization, and the full NN/DN layer
calculation with explicit selected-edge counts. It also develops
initial-vertex inheritance and right-endpoint attachment in detail. Its opening
states the component theorem, and its final sections give prefix selection,
the four first-contact cases, attachment measure decrease and the final
component induction. Preparation and restored-exterior crossing slides now have
full proofs, including the recovery of all corner covers after each chain and
the right-before-left restoration used by Lean. The parallel-edge and two-chain
lemmas, and the explicit avoiding paths proving good-edge removability, are
now written in detail. The complete-diagram base now includes chain insertion,
interval opening/lifting/closing, outer-chord moves and the four explicit
five-vertex paths. Last-clique inheritance now includes connected-core
preparation, sweep/lift/restoration, the fixed spanning tree and both kinds
of extra-edge exchange. A whole-proof dependency and notation audit has returned; its attachment,
inheritance and induction clarifications are incorporated. The component section forms the second part of the combined paper. The mathematical source is the
[assembled proof](../proofs/COMPONENT_DIAGRAM_COMPLETION.md).

The independent diagram formalization is complete, including the final
induction and weighted positivity consequences. See the
[completion audit](../DIAGRAM_PROOF_COMPLETION.md) for the verified scope and
current 815-query axiom audit, including the circular component consequences. Compiler status and source correspondence stay here
and in the formalization plan, outside the manuscript prose.

| Draft construction | Lean correspondence | Current scope |
| --- | --- | --- |
| Figure 1: diamond as a restricted sum | `diamond_hrv_maps`, `markedK_diamond`, `markedE_diamond` | Checked with arbitrary exterior; no cover hypothesis |
| Preparation in decreasing chain-terminal order | `CornerFamily.exists_prepareChain`, `exists_preparation`, `exists_anchor_in_component` | Checked actual flips; good edges retained; all corners cover after each complete chain |
| Figure 2: crossing sweeps and full restoration | `exists_crossingSlide`, `crossingSlide_mem_component` | Checked exact exchanged endpoint; draft and figure restore right sweep before left |
| Figure 3: fixed-count rearrangement within a chain pair | `copy_reachable_undirected`, `anchors_connected_of_occupancy` | Checked restored crossing slides; canonical packing is an exposition of these exchanges |
| Figure 4: complete-diagram chain construction | `exists_complete_chain`, `exists_connected_prefix_of_single_corner` | Checked fork elimination, child merge and prefix induction |
| Complete-diagram interval and chord paths | `complete_interval_chain_path`, `completeChainState_reachable_of_fixed_outer`, `completeChainState_outerChord_reachable`, `completeChainState_singleChord_reachable`, `complete_reachable_five`, `complete_reachable` | Checked; the detailed draft uses the same moves and finite base paths |
| Last-clique connected core and restored exterior | `exists_reachable_connected_lastClique_core`, `exists_lastClique_anchor_replacement_preserving_anchor` | Checked; smaller-core uniqueness is the explicit inheritance hypothesis |
| Figure 5: fixed core tree and omitted leaves | `exists_lastClique_core_tree`, `exists_lastClique_tree_replacement`, `lastCliqueFixedEdges_isTree` | Checked; the figure fixes a concrete selected tree in each diagram |
| Last-clique extra-edge exchanges and inheritance | `exists_last_clique_shared_exchange`, `anchors_connected_of_overlapping_extra_positions`, `commonCover_connected_of_lastClique_core` | Checked; the draft retains the temporary repair of the missing star edge and restores the full tree at endpoints |
| Removing one good normal edge | `goodEdge_weakReach_avoiding_terminal`, `weakReach_erase_good_edge`, `goodEdgeGraph_delete_connected` | Checked two-edge replacement, skipped-chain path and third-chain detour |
| Three smaller corrections and envelope | `certifies_of_not_hasCommonWitness` | Checked whole-component certificates; included in final axiom audit |
| Figure 7: NN/DN layer sums and component isolation | `NNContact.layer`, `DNContact.layer`, `certifies_of_layer`, `certifies_nn`, `certifies_dn` | Checked full layers and isolated whole-component certificates; final axiom audit passed |
| Restrict after deleting zero | `initialVertex_anchor_restrict`, `induced_allCorners_initialVertex` | Checked |
| Make the selected core connected | `CornerFamily.exists_reachable_connected_initialVertex_core` | Checked actual crossing-slide paths |
| Keep initial extras fixed along a core path | `initialVertex_lift_reachable`, `initialVertex_reachable_of_same_initial_row` | Checked under smaller-core uniqueness |
| Figure 6: initial crossing-slide endpoint | `initialVertex_row_of_exchange`, `initialVertex_restrict_of_exchange` | Checked exact selected-edge identities |
| Choose the missing-edge witness and connect neighboring extra sets | `CornerFamily.exists_initialVertex_adjacent`, `initialVertex_reachable_of_erase_initial_row` | Checked under the stated removability/core-uniqueness hypotheses |
| Connect all feasible extra sets | `initialVertex_connected_core_anchors` | Checked actual assembly under the stated core hypotheses |
| Initial-vertex inheritance for common-cover states | `commonCover_connected_of_initialVertex_core` | Checked preparation, sector paths and reversed target preparation |
| Preserve chain count and discharge matching-edge removability | `CornerFamily.initialVertex_fixedTerminal_card`, `commonCover_connected_of_initialVertex_short` | Checked under short-edge and three-chain hypotheses, leaving smaller-core uniqueness |
| Preserve short edges in the canonical last-clique core | `lastClique_induced_short_naturalEdges` | Checked; used in the reversed first-clique induction |
| At most two corner chains | `CornerFamily.commonCover_connected_of_terminal_card_le_two` | Checked; detailed preparation/one-pair rearrangement proof in draft |
| Common-cover uniqueness without articulation | `commonCoverUnique_of_shortEdges` | Checked vertex-count induction; final axiom audit passed |
| Extension through an initial path | `commonCoverUnique_of_initialPathBlock` | Checked pendant-path extension; final axiom audit passed |
| Endpoint-marked K and E | `markedK`, `markedE`, `markedK_diamond`, `markedE_diamond` | Existing checked semantics; see plan for the P2 interfaces |
| Figure 8: attachment and fibre merger | `IsRightAttachment.flipComponent_glue`, `hrv_glue_left`, `hrv_glue_right`, `attach_transfer` | Checked at `26b2d97`: whole product components, marked K/E transfer and measure decrease |
| Figure 9: first nontrivial prefix and fixed attachment | `exists_prefix`, `uCertifies_of_witness`, `attach_measure_lt` | Checked prefix coverage and attached certificate with strict measure decrease |
| Whole-component corrections and marked recurrences | `certifies_of_not_hasCommonWitness`, `certifies_nn`, `certifies_dn` | Checked; integrated into the final induction |
| First-drop coverage and final expansion | `certifies_firstDrop`, `component_eq_by_diagrams_aux`, `component_strict_eq_elementary_of_forward` | Checked for every ordinary diagram and every whole component |

The [circular component subsections](CIRCULAR_COMPONENTS.md) finish the second
part. They give the finite signed expansion, constancy on actual components,
and the compatible-lift preimage as a union of whole ordinary components.
Strict markings are removed before arbitrary subset sums. The HRV deletion
identity is proved by a sign-reversing toggle preserving the entire lifted
map; it is not inferred just from the aggregate circular theorem.

| Circular component construction | Related Lean | Scope |
| --- | --- | --- |
| Simultaneous coloring and entire-HRV expansion | `strictOrderEnumerator_finiteCompanion`, `liftedHRV_value_finiteCompanion` | All acyclic selected states, with undecoration made explicit |
| Balanced base and coefficient cancellation | `coefficient_eq_delta_of_balanced`, `sum_powerset_coefficient_eq_zero`, `sum_powerset_cyclicNegative_eq_zero_of_gain_excess` | Actual edge instances, negative-cycle gains and weak-component signs |
| Coefficient constancy under actual circular flips | `componentCoefficient_eq_of_mem_flipComponent` | Tight potentials reconstruct both full cover tests and preserve the original component |
| Compatible lift sorting and semantic transport | `orientationFromCompatible_injective`, `orientationFromCompatible_hrvMonomial`, `orientationFromCompatible_strictOrderEnumerator` | Injective state transport and exact finite fibre sizes |
| Group the preimage by whole ordinary components | `compatibleComponentPreimage_closed`, `component_identity_of_forward_components` | A union of components, not an assumed single component |
| Final circular identity and positivity | `component_strict_eq_elementary`, `component_weighted_e_positive` | Every circular diagram, every actual component and every finite alphabet |

The circular source map supplements [the completion audit](../CIRCULAR_COMPLETION.md):

| Draft construction | Related Lean | Scope |
| --- | --- | --- |
| Circular expansion theorem | `Circular/Expansion.lean`, `coloringLLT_shifted_eq_orientation_sum` | Checked aggregate theorem |
| Four selected triangles | `Circular/HRVTriangle.lean`, `tri_local_identity` | Integer-cover HRV identity |
| Figure 1: direct NN/DN coloring relations | `naturalPairs_erase_map_swap`, `firstBounce_strict_exterior_swap`, `coloringLLT_firstBounce_geometry`, `coloringLLT_dnSuccessor` | Checked; the draft spells out boundary avoidance and all coloring-ascent cases |
| Figure 2: DD resolution and contact-count induction | `DDLocalData.coloring_resolution`, `orientation_resolution`, `resolved_dd_child`, `delete_dd_child`, `coloring_closing_nn`, `dnModelsClaim_succ` | Checked; the resolved child's doubled area increases by one, so it is not an outer-induction step |
| Separated ND contacts | `NDSeparatedHyp.dS_dQ_models`, `xQShift_coloringLLT_nd`, `shiftedOrientationExpansion_nd` | Seven identities, cyclic case and final area decreases written explicitly |
| Terminal-contact reduction | `Circular/AliasRecurrences.lean`, `Diagram.exists_nd_alias_reduction`; `AliasReductionForced.lean`, `card_B`, `card_C` | Common factor `1+q`, doubled-area decrease six |
| Interior column reversal | `Circular/InteriorReversalReduction.lean`, `Diagram.expansion_of_nd_interior_overlap` | Strict interior intersection; terminal contact treated separately |
| Reversal boundary checks | `reversalAreaValues_cyclic`, `boundary_not_inside_column`, `boundaryNaturalLift_reversal_iff` | Explicit column-end decrements, unique boundary row, sink exception and source exception |
| Internal-edge factor cancellation | `Circular/ComponentFactorization.lean`, `Diagram.expansion_iff_component_residual` | Different source/target exponents allowed |
| Area and rank induction | `Circular/GeometricArea.lean`, `Diagram.doubledArea`; `NeutralTransport.lean`, `Diagram.strictRank` | Draft `J` is exactly the sum of proper-ancestor count times strict-edge length |

The ordinary section uses greatest reachable vertices in the ordinary order.
The circular section uses greatest reachable integers followed by reduction
modulo the period. The first part proves the aggregate theorem. The second part proves the
ordinary component theorem by diagrams and then the circular component
theorem through the finite companion.

The [diagram macros and usage guide](tex/README.md) implement the user's
restricted-sum convention. A diagram specifies selected/absent/optional/strict
edges, forbidden natural pairs, cover conditions, total-size layers and endpoint
colors. Gray/white ambient regions distinguish unweighted and normal-edge-weighted sums.
The two-page `diagram-examples.tex` preview and the diamond and NN/DN figures
compile without warnings or box overflows and were visually inspected.

All SVG figures now have native `.tex` sources in `tex/`; the cell figures
use `llt-diagrams.sty`. Edit those sources rather than the generated SVG
font paths. Their PNG previews live in the external request cache, and all
figures have been visually inspected. The
cell figure follows the diagonal-label and selected-cell convention of the
paper with Robin; its retained arrows indicate corner covers at the two
displayed endpoints.

## Rebuilding the manuscript

The Markdown sections are the canonical prose. Native figure sources live
in `tex/`; SVGs in `figures/` are previews. The assembler assigns distinct
circular/ordinary equation labels, resolves cross-section links and converts
local figure numbering to a single sequence. It does not alter mathematical
expressions beyond those labels. No generated build output belongs in Git.

Use semantic fenced divisions for mathematical statements and proofs:

```markdown
::: {.lemma #lem:stableLabel title="Descriptive title"}
The statement, with its hypotheses.
:::

::: {.proof}
The proof.
:::
```

The assembler emits actual `amsthm` environments, sharing a counter within
each section. Supported classes are `theorem`, `lemma`, `proposition`,
`corollary`, `definition`, `example`, `remark` and `proof`. Titles are
optional. Use `\ref{lem:stableLabel}` for numbered references and `\defin`
at first definitions. Figures can occur inside proofs. The assembler checks
environment conversion, unique labels and reference targets before compiling.

With Python 3, Pandoc and TeX Live (`latexmk`, `pdflatex`, `bibtex`) installed:

```sh
python3 docs/drafts/build_manuscript.py --output /external/path/llt-draft
```

Use `--no-compile` to assemble TeX only. Output must be outside the source
checkout. The command writes `manuscript.pdf`, editable `manuscript.tex`, all
native vector figures, a SHA256 source manifest and `manuscript-source.zip`.
The zip contains the complete TeX source and canonical Markdown input. Compile
its `manuscript.tex` directly with `latexmk -pdf manuscript.tex`, or regenerate
from the bundled canonical sources. The bundle includes the authors and AI statement.

Current revised preview directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/manuscript-revision/`.
The tagged baseline remains in the sibling `manuscript/` directory.
The independent reviews approved the aggregate proof, ordinary induction,
circular companion, and the final theorem scopes. The assembled PDF has
thirteen vector figures. Its final build and layout checks are recorded in
`HANDOFF.md`.

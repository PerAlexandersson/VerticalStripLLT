# Verified circular results

The full coloring–HRV equality remains open. This table records completed
uniform results; [CIRCULAR_GOALS.md](CIRCULAR_GOALS.md) contains only the
remaining work. Names below lie under `VerticalStripLLT.Circular` unless
otherwise indicated. Current build and axiom counts are in [HANDOFF](../HANDOFF.md).

| Result | Checked interface |
| --- | --- |
| Faithful circular data and coloring sum | `CircularArea`, `Edge`, `Diagram`, `EdgeData.coloringLLT`; [Diagram](../VerticalStripLLT/Circular/Diagram.lean), [Coloring](../VerticalStripLLT/Circular/Coloring.lean) |
| Coloring expansion over selected edge subsets | `finite_subset_coloring_expansion`; [SubsetExpansion](../VerticalStripLLT/Circular/SubsetExpansion.lean), [OrientationSum](../VerticalStripLLT/Circular/OrientationSum.lean) |
| Actual integer-cover highest reachable vertex | `liftedHRV`, greatest-reachability and periodicity theorems; [HRV](../VerticalStripLLT/Circular/HRV.lean), [HRVRoots](../VerticalStripLLT/Circular/HRVRoots.lean) |
| Degree and nonnegative coefficients of the independent HRV expression | `shiftedOrientationExpansion_isWeightedHomogeneous_degree`, `shiftedOrientationExpansion_coeff_nonneg`; [HRVDegree](../VerticalStripLLT/Circular/HRVDegree.lean), [HRVPositive](../VerticalStripLLT/Circular/HRVPositive.lean) |
| Empty normal selection in any diagram | `strictOrderEnumerator_eq_eval_hrvMonomial_of_empty`; actual strict-chain HRV fibers in [StrictExpansion](../VerticalStripLLT/Circular/StrictExpansion.lean), [StrictFibers](../VerticalStripLLT/Circular/StrictFibers.lean) |
| Strict cycles contribute zero | [StrictCycleVanishing](../VerticalStripLLT/Circular/StrictCycleVanishing.lean), [StrictCycleExpansion](../VerticalStripLLT/Circular/StrictCycleExpansion.lean) |
| Full no-normal-edge semantic base | `Diagram.coloringLLT_shifted_eq_expansion_of_no_normal`; [ZeroAreaExpansion](../VerticalStripLLT/Circular/ZeroAreaExpansion.lean) |
| Independent R1 identities and area decreases | [CornerDiagram](../VerticalStripLLT/Circular/CornerDiagram.lean), [CornerDeleteOrientation](../VerticalStripLLT/Circular/CornerDeleteOrientation.lean), [CornerMeasure](../VerticalStripLLT/Circular/CornerMeasure.lean) |
| Complete reverse search, including restarts | `Diagram.exists_complete_reverseBounce`; [BounceSearch](../VerticalStripLLT/Circular/BounceSearch.lean) |
| Full neutral-bounce termination | `FullNeutralBounce.strictRank_lt`, `strict_cycle_of_infinite_full_neutral_bounce`; [NeutralTermination](../VerticalStripLLT/Circular/NeutralTermination.lean) |
| Mixed DD/neutral auxiliary termination and vanishing | `LocalEliminationStep.measure_lt`, `strict_cycle_of_infinite_local_elimination`, `coloringLLT_eq_zero_of_infinite_local_elimination`; [LocalEliminationTermination](../VerticalStripLLT/Circular/LocalEliminationTermination.lean) |
| Valid full DN successor and geometric measure | `Diagram.exists_area_preserving_dn`; [GeometricArea](../VerticalStripLLT/Circular/GeometricArea.lean) |
| Direct NN for both actual models | `Diagram.expansion_of_firstBounce_NN`; [FirstBounceRecurrences](../VerticalStripLLT/Circular/FirstBounceRecurrences.lean), [ShortenStrictMeasure](../VerticalStripLLT/Circular/ShortenStrictMeasure.lean) |
| Direct DN for both actual models | `Diagram.expansion_iff_secondBounce`; [SecondBounceRecurrences](../VerticalStripLLT/Circular/SecondBounceRecurrences.lean) |
| DD count and NN/DN contact separation | `Diagram.reverseBounce_iff_counted`, `RawBounceContacts.main_parallel_disjoint`; [CountedBounce](../VerticalStripLLT/Circular/CountedBounce.lean), [RawBounceContacts](../VerticalStripLLT/Circular/RawBounceContacts.lean) |
| DD local resolution and complete deletion child | `Diagram.exists_ddLocalData`, `DDLocalData.coloring_resolution`, `orientation_resolution`, `Diagram.delete_dd_child`; [DDLocalRealization](../VerticalStripLLT/Circular/DDLocalRealization.lean), [DDDeletedChild](../VerticalStripLLT/Circular/DDDeletedChild.lean) |
| Exact resolved DD rows | `DDLocalData.resolved_area`, `resolved_boundary_rows`, `resolved_strictAt_iff`; [DDResolvedRows](../VerticalStripLLT/Circular/DDResolvedRows.lean), [DDResolvedStrict](../VerticalStripLLT/Circular/DDResolvedStrict.lean) |
| Complete resolved DD child for NN/DN | `DDLocalData.resolved_dd_child`, `resolved_admissible`; [DDResolvedChild](../VerticalStripLLT/Circular/DDResolvedChild.lean), [DDResolvedTransport](../VerticalStripLLT/Circular/DDResolvedTransport.lean), [BounceIterates](../VerticalStripLLT/Circular/BounceIterates.lean) |
| Interior overlap restarts at one bounce | `DDLocalData.exists_oneBounce_restart_of_interior_overlap`; [InteriorRestart](../VerticalStripLLT/Circular/InteriorRestart.lean) |
| Exact DD half-square accounting and semantic assembly | `DDLocalData.resolved_doubledArea`, `deleted_doubledArea`, `expansion_of_children`; [DDResolvedMeasure](../VerticalStripLLT/Circular/DDResolvedMeasure.lean), [DDRecurrences](../VerticalStripLLT/Circular/DDRecurrences.lean) |
| Uniform direct ND constructor geometry | `Diagram.exists_ndLocalData`, `lowerStrict_strictAt_iff`, `lowerStrict_boundary`; [NDLocalData](../VerticalStripLLT/Circular/NDLocalData.lean), [LowerStrictRows](../VerticalStripLLT/Circular/LowerStrictRows.lean) |
| Complete overlapping ND induction step | `Diagram.exists_nd_alias_reduction`, `Diagram.expansion_of_nd_alias`, `AliasContacts.target_admissible_iff`; actual coloring/HRV factors and doubled-area drop six in [AliasRecurrences](../VerticalStripLLT/Circular/AliasRecurrences.lean) |
| Forced ascent/descent factors for actual models | [ForcedColoring](../VerticalStripLLT/Circular/ForcedColoring.lean), [ForcedOrientation](../VerticalStripLLT/Circular/ForcedOrientation.lean) |

Theorem explanations remain in [proofs/](README.md#proof-explanations).
Early examples are isolated in `VerticalStripLLT/Examples/` and excluded from
the main library imports. Historical planning and request records do not
constitute proof; every result listed above passed the local pinned toolchain.

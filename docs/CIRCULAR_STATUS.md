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
| Strict cycles contribute zero | [StrictCycleVanishing](../VerticalStripLLT/Circular/StrictCycleVanishing.lean), [StrictCycleExpansion](../VerticalStripLLT/Circular/StrictCycleExpansion.lean) |
| Full no-normal-edge semantic base | `Diagram.coloringLLT_shifted_eq_expansion_of_no_normal`; [ZeroAreaExpansion](../VerticalStripLLT/Circular/ZeroAreaExpansion.lean) |
| Independent R1 identities and area decreases | [CornerDiagram](../VerticalStripLLT/Circular/CornerDiagram.lean), [CornerDeleteOrientation](../VerticalStripLLT/Circular/CornerDeleteOrientation.lean), [CornerMeasure](../VerticalStripLLT/Circular/CornerMeasure.lean) |
| Complete reverse search, including restarts | `Diagram.exists_complete_reverseBounce`; [BounceSearch](../VerticalStripLLT/Circular/BounceSearch.lean) |
| Full neutral-bounce termination | `FullNeutralBounce.strictRank_lt`, `strict_cycle_of_infinite_full_neutral_bounce`; [NeutralTermination](../VerticalStripLLT/Circular/NeutralTermination.lean) |
| Valid full DN successor and geometric measure | `Diagram.exists_area_preserving_dn`; [GeometricArea](../VerticalStripLLT/Circular/GeometricArea.lean) |
| Direct NN for both actual models | `Diagram.expansion_of_firstBounce_NN`; [FirstBounceRecurrences](../VerticalStripLLT/Circular/FirstBounceRecurrences.lean), [ShortenStrictMeasure](../VerticalStripLLT/Circular/ShortenStrictMeasure.lean) |
| Direct DN for both actual models | `Diagram.expansion_iff_secondBounce`; [SecondBounceRecurrences](../VerticalStripLLT/Circular/SecondBounceRecurrences.lean) |
| DD count and NN/DN contact separation | `Diagram.reverseBounce_iff_counted`, `RawBounceContacts.main_parallel_disjoint`; [CountedBounce](../VerticalStripLLT/Circular/CountedBounce.lean), [RawBounceContacts](../VerticalStripLLT/Circular/RawBounceContacts.lean) |
| Valid overlapping ND target and exact area decrease | `Diagram.exists_aliasTarget_of_reverseBounce`; [AliasRealization](../VerticalStripLLT/Circular/AliasRealization.lean), [AliasMeasure](../VerticalStripLLT/Circular/AliasMeasure.lean) |
| Forced ascent/descent factors for actual models | [ForcedColoring](../VerticalStripLLT/Circular/ForcedColoring.lean), [ForcedOrientation](../VerticalStripLLT/Circular/ForcedOrientation.lean) |

Theorem explanations remain in [proofs/](README.md#proof-explanations).
Early examples are isolated in `VerticalStripLLT/Examples/` and excluded from
the main library imports. Historical planning and request records do not
constitute proof; every result listed above passed the local pinned toolchain.

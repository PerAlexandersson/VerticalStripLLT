# Documentation

## Verified results

| Subject | Proof and verification | Source or module map |
| --- | --- | --- |
| Ordinary LLT expansion | [Completion audit](COMPLETION.md) | [Source map](FORMALIZATION.md) |
| Circular LLT expansion | [Completion audit](CIRCULAR_COMPLETION.md) | [Verified results](CIRCULAR_STATUS.md) |
| All flip-component expansions | [Completion audit](COMPONENT_COMPLETION.md) | [Module map](COMPONENT_FORMALIZATION.md) |

These results include shifted elementary positivity and weighted degree.
The component result is the finite strict/e identity on actual complete components.

## Proof sources

- [Ordinary component word proof](proofs/COMPONENT_ORDINARY_PROOF.md).
- [Alternative diamond proof search](proofs/COMPONENT_AUXILIARY_DIAMONDS.md):
  proved auxiliary reductions; the general component step remains open.
- [Local recurrence diagrams](proofs/COMPONENT_LOCAL_DIAGRAMS.md): the two
  four-vertex NN overlaps and the proved five-vertex reduction of DN target
  comparisons after source balance, with arbitrary exterior and cycle rank.
- [Direct NN redistribution](proofs/COMPONENT_NN_REDISTRIBUTION.md):
  one-component split, a three-diamond worked proof, and exact Rust certificates.
- [NN tree components](proofs/COMPONENT_NN_TREE_SECTORS.md): the connected
  tree component maps to complete smaller forest components; selected-r
  target trees already have constant coefficients for every source component.
- [Complete unicyclic NN step](proofs/COMPONENT_NN_LEFT_REASSEMBLY.md):
  the incoming-edge induction and paired exposure finish the left comparison;
  the repaired image of one component is a sum of whole smaller components
  with the same coloring/HRV coefficients. Higher ranks and DN/DD remain open.
- [Unicyclic NN reassembly](proofs/COMPONENT_NN_UNICYCLIC_REASSEMBLY.md):
  one simultaneous repair completes all r-absent pieces and preserves the
  settled comparisons; the subsequent left comparison completes the proof.
- [Active-component NN swaps](proofs/COMPONENT_NN_ACTIVE_SWAP.md):
  normalized tree extensions prove the full adjacent swap and settle every
  right first comparison, used in the complete unicyclic NN step.
- [NN triangle overlaps](proofs/COMPONENT_NN_OVERLAPS.md): only two flip
  geometries remain; proved local corrections and their compatibility gap.
- [Left NN transfer](proofs/COMPONENT_NN_LEFT_TRANSFER.md): four diamonds
  transfer a left difference to a right difference, with explicit remainders.
- [NN flip interactions](proofs/COMPONENT_NN_FLIP_INTERACTIONS.md): commuting
  square criteria and decreasing diamond identities for shared-edge cases.
- [Four-edge cases](proofs/COMPONENT_FOUR_EDGE_CASES.md): a sixteen-row NN
  table repaired into whole components, and a repair with attached components.
- [Overlapping corners](proofs/COMPONENT_OVERLAPPING_CORNERS.md): two further
  component recurrences, with a simultaneous repair and exterior extension.
- [Closure repair tests](proofs/COMPONENT_CLOSURE_REPAIR_TESTS.md): exact
  component reconstructions and counterexamples to extremal restrictions.
- [Unicyclic redundancy](proofs/COMPONENT_UNICYCLIC_REDUNDANCY.md): a
  tree reduction, a classification of mixed-cyclic components, and two
  proved families of NN whole-component corrections.
- [Four-cycle swap](proofs/COMPONENT_FOUR_CYCLE_SWAP.md): actual flip
  paths for arbitrary attached trees, both second mixed NN joins,
  and an adjacent swap theorem for longer unicyclic states.
- [Unicyclic natural blocks](proofs/COMPONENT_UNICYCLIC_BLOCKS.md):
  strict-chain contraction, a five-flip envelope repair, and finite
  evidence for the unresolved uniqueness question without articulation.
- [Moving one outgoing edge](proofs/COMPONENT_RIGHT_ARM_TRANSFER.md):
  an ordinary unicyclic repair requiring no NN eligibility or strict
  retained edge, with bypass sweeps and an incoming-edge counterexample.
- [Leftmost unicyclic NN recurrence](proofs/COMPONENT_LEFTMOST_NN_UNICYCLIC.md):
  packet isolation and a signed recurrence in whole smaller components,
  valid simultaneously for the coloring and HRV sums.
- [Incoming-edge repairs](proofs/COMPONENT_INCOMING_EDGE_TRANSFER.md):
  a selected containing interval suffices, including two bypass repairs.
- [General NN inactive corrections](proofs/COMPONENT_NN_INACTIVE_CORRECTIONS.md):
  all inactive-corner neighbor cases, redundant middle images, and
  rightward q-exits, used in the complete unicyclic NN step.
- [Leftward NN transition](proofs/COMPONENT_LEFT_EXIT.md): containing
  corners, tree normalization and induction on an incoming vertex handle
  a leftward q-exit that exposes the strict corner.
- [General NN middle joins](proofs/COMPONENT_NN_MIDDLE_JOINS.md): three
  forest constructions give an exposing witness and close every active
  middle join in cycle rank one; first mixed joins remain open.
- [NN trees and incoming bridges](proofs/COMPONENT_NN_FIRST_JOINS.md):
  tree comparisons lift through the full diagram; a strict covering
  container anywhere gives the incoming-bridge repair, then both first joins
  for mixed-acyclic representatives whose cycle avoids the adjacent vertices.
- [NN sink repair](proofs/COMPONENT_NN_SINK_REPAIR.md): cut-and-replace
  tree comparisons and branch moves identify the adjacent-swap piece when
  the unique cycle meets an adjacent vertex as a sink.
- [Path-square components](proofs/COMPONENT_PATH_SQUARE.md): all edge-count
  components, an explicit elementary formula, and terminal cases of
  arbitrary cycle rank.
- [Redundancy diamond](proofs/COMPONENT_REDUNDANCY_DIAMOND.md): exact
  union/intersection formulas and a reduction when two cycles exchange redundancy.
- [Whole-component corrections](proofs/COMPONENT_GLOBAL_REASSEMBLY.md):
  a larger NN reconstruction and a criterion for inactive tree extensions.
- [Component recurrence continuation](proofs/COMPONENT_RECURRENCE_REDUCTION.md):
  ordinary NN and DN packets, known corrections, and the remaining isolation question.
- [DD component packets](proofs/COMPONENT_DD_PACKETS.md): exact corner sectors
  and a decreasing ordinary area/moment order; individual redistribution remains open.
- [Finite circular companion](proofs/COMPONENT_FINITE_COMPANION.md).
- [Overleaf comparison](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md): direct HRV
  extraction and the alternative bounded-face argument.
- [Circular column reversal](proofs/CIRCULAR_COLUMN_REVERSAL.md): the aggregate induction.

## Challenges, notes and provenance

- [Challenge](../CHALLENGE.md): a precise target for a shorter proof.
- [Streamlining audit](PROOF_STREAMLINING.md): shared lemmas and the second cleanup pass.
- [Research catalogue](RESEARCH_NOTES.md): detailed notes, alternative routes,
  counterexamples and archived work. Historical open claims are not current blockers.
- [Restricted recurrence audit](RESTRICTED_BOUNCE_AUDIT.md): an unused, separate open claim.
- [Aristotle ledger](ARISTOTLE.md): external candidates and their verification.
- [Handoff](../HANDOFF.md): current ownership, checkpoints and build logs.

[Manuscript synchronization](MANUSCRIPT.md) records the current Overleaf draft,
its proof correspondence and diagram/build checks.

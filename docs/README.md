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
- [Direct NN redistribution](proofs/COMPONENT_NN_REDISTRIBUTION.md):
  one-component split, a three-diamond worked proof, and exact Rust certificates.
- [NN triangle overlaps](proofs/COMPONENT_NN_OVERLAPS.md): only two flip
  geometries remain; proved local corrections and their compatibility gap.
- [Left NN transfer](proofs/COMPONENT_NN_LEFT_TRANSFER.md): four diamonds
  transfer a left difference to a right difference, with explicit remainders.
- [NN flip interactions](proofs/COMPONENT_NN_FLIP_INTERACTIONS.md): commuting
  square criteria and decreasing diamond identities for shared-edge cases.
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

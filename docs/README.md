# Documentation

## Current recurrence proof

Start with [Component e-positivity by recurrence](proofs/COMPONENT_RECURRENCE_OUTLINE.md).
It gives the target identity, component maps, a complete worked example,
induction order, and exact remaining proof obligations. The general recurrence
proof is unfinished; the separate verified component theorem remains complete.

| Piece | Read next |
| --- | --- |
| Author's diagram maps | [Notebook source map](proofs/COMPONENT_NOTEBOOK_MAP.md) |
| NN: split, repair, collect | [Worked construction](proofs/COMPONENT_NN_REDISTRIBUTION.md), [complete unicyclic step](proofs/COMPONENT_NN_LEFT_REASSEMBLY.md) |
| DN: push one component | [Direct split and overlaps](proofs/COMPONENT_DN_DIRECT_OVERLAPS.md) |
| DN: repair its pieces | [Joint diamonds](proofs/COMPONENT_DN_JOINT_REPAIRS.md), [source additions](proofs/COMPONENT_DN_SOURCE_ADDITIONS.md), [retained edges](proofs/COMPONENT_DN_RETAINED_EDGE.md) |
| DD and the induction order | [Corner split and measure](proofs/COMPONENT_DD_PACKETS.md) |
| Choosing a recurrence for every ordinary diagram | [First-drop coverage and conditional induction](proofs/COMPONENT_RECURRENCE_COVERAGE.md) |

[Detailed component catalogue](COMPONENT_NOTE_CATALOGUE.md) retains all the
supporting notes, earlier constructions and local examples. The outline
explains where each principal result enters the argument.

## Verified results

| Subject | Proof and verification | Source or module map |
| --- | --- | --- |
| Ordinary LLT expansion | [Completion audit](COMPLETION.md) | [Source map](FORMALIZATION.md) |
| Circular LLT expansion | [Completion audit](CIRCULAR_COMPLETION.md) | [Verified results](CIRCULAR_STATUS.md) |
| All flip-component expansions, by diagrams | [Completion audit](DIAGRAM_PROOF_COMPLETION.md) | [Module map](LEAN_COORDINATION.md) |
| The same expansions, by the earlier word proof | [Completion audit](COMPONENT_COMPLETION.md) | [Module map](COMPONENT_FORMALIZATION.md) |

These include the finite strict/e component identity, shifted elementary
positivity and weighted degree. Both proofs are complete and import-disjoint.
The diagram proof follows the
[draft](drafts/ORDINARY_COMPONENT_DIAGRAM_PROOF.md) and carries the plain
theorem names. The [ordinary word proof](proofs/COMPONENT_ORDINARY_PROOF.md)
gives the `_by_words` theorems. Both reach all circular components through the
[finite circular companion](proofs/COMPONENT_FINITE_COMPANION.md).

## Manuscript, provenance and recovery

- [Manuscript synchronization](MANUSCRIPT.md): Overleaf drafts and source maps.
- [Research catalogue](RESEARCH_NOTES.md): broader research and historical notes.
- [Challenge](../CHALLENGE.md) and [streamlining audit](PROOF_STREAMLINING.md).
- [Current handoff](../HANDOFF.md): ownership, next proof step and verification.

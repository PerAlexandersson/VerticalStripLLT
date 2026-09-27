# Circular completion and downstream work

The full aggregate HRV formula and e-positivity are proved in
`Circular/Expansion.lean`, for every circular diagram and finite alphabet.
The full build and all 2037 axiom checks pass. See the
[completion audit](CIRCULAR_COMPLETION.md), [verified results](CIRCULAR_STATUS.md),
and [column-reversal proof](proofs/CIRCULAR_COLUMN_REVERSAL.md).
There are no remaining proof obligations for the aggregate theorem.

The [ordinary flip-component identity](proofs/COMPONENT_ORDINARY_PROOF.md)
and the full [circular identity](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md) now
have independently audited mathematical proofs. The circular proof comes
from the Overleaf v9 draft: its bounded-face coefficients regroup into whole
components admitting compatible lifts. Both full component formalizations
remain unfinished. At the user's request we obtained and independently audited
a [finite gain-graph companion](proofs/COMPONENT_FINITE_COMPANION.md) proving
the same coefficient identity and component isolation without polyhedra.
See the [Lean plan](COMPONENT_FORMALIZATION.md),
[current proof status](FLIP_COMPONENT_STATUS.md), and
[component interfaces](CIRCULAR_FLIPS.md).

The older manuscript proof outline also needs to be aligned with the checked
half-square induction and interior column reversal. Historical paired-child
and no-wrap proof-search notes are retained as provenance, not an active agenda.
The aggregate theorem does not prove their unused auxiliary claims.

No new examples or general symmetric-functions library are planned. Current
ownership and verification logs are recorded in [HANDOFF](../HANDOFF.md).

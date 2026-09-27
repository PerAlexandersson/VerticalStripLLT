# Circular completion and downstream work

The full aggregate HRV formula and e-positivity are proved in
`Circular/Expansion.lean`, for every circular diagram and finite alphabet.
The full build and all 2037 axiom checks pass. See the
[completion audit](CIRCULAR_COMPLETION.md), [verified results](CIRCULAR_STATUS.md),
and [column-reversal proof](proofs/CIRCULAR_COLUMN_REVERSAL.md).
There are no remaining proof obligations for the aggregate theorem.

The [ordinary flip-component identity](proofs/COMPONENT_ORDINARY_PROOF.md)
now has a complete independently audited mathematical proof. Compatible-lift
transport also proves the balanced circular component case. These new
component results are not yet Lean-verified. The remaining mathematical
target is the primitive unbalanced circular component formula; the ordinary
word proof has not been extended to the periodic setting. See the
[current proof status](FLIP_COMPONENT_STATUS.md) and the exact
[component interfaces](CIRCULAR_FLIPS.md). Weak/strict omega translation
remains a separate formal bridge.

The older manuscript proof outline also needs to be aligned with the checked
half-square induction and interior column reversal. Historical paired-child
and no-wrap proof-search notes are retained as provenance, not an active agenda.
The aggregate theorem does not prove their unused auxiliary claims.

No new examples or general symmetric-functions library are planned. Current
ownership and verification logs are recorded in [HANDOFF](../HANDOFF.md).

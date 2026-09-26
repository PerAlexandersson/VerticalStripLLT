# Circular completion and downstream work

The full aggregate HRV formula and e-positivity are proved in
`Circular/Expansion.lean`, for every circular diagram and finite alphabet.
The full build and all 2037 axiom checks pass. See the
[completion audit](CIRCULAR_COMPLETION.md), [verified results](CIRCULAR_STATUS.md),
and [column-reversal proof](proofs/CIRCULAR_COLUMN_REVERSAL.md).
There are no remaining proof obligations for the aggregate theorem.

The next research task is the full flip-component identity. Its exact target
and proved foundations are retained in [CIRCULAR_FLIPS.md](CIRCULAR_FLIPS.md).
A complete component proof is not known here and must not be assumed; audit
the proposed argument before deciding the next implementation goals.
Weak/strict omega translation is a separate bridge.

The older manuscript proof outline also needs to be aligned with the checked
half-square induction and interior column reversal. Historical paired-child
and no-wrap proof-search notes are retained as provenance, not an active agenda.
The aggregate theorem does not prove their unused auxiliary claims.

No new examples or general symmetric-functions library are planned. Current
ownership and verification logs are recorded in [HANDOFF](../HANDOFF.md).

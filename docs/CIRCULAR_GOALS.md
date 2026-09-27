# Circular completion and downstream work

The full aggregate HRV formula and e-positivity are proved in
`Circular/Expansion.lean`, for every circular diagram and finite alphabet.
The aggregate completion checkpoint passed its build and 2037 axiom checks. See the
[completion audit](CIRCULAR_COMPLETION.md), [verified results](CIRCULAR_STATUS.md),
and [column-reversal proof](proofs/CIRCULAR_COLUMN_REVERSAL.md).
There are no remaining proof obligations for the aggregate theorem.

The ordinary and full circular component identities, shifted weights,
elementary positivity and degree are also proved. The integrated route uses
the ordinary word argument with direct signed-sink extraction, the finite
gain-graph companion, and compatible ordinary preimages closed under flips.
No proof obligation remains for these component theorems. See the
[component completion audit](COMPONENT_COMPLETION.md) for public declarations,
source correspondence and final checks (2074 library jobs, 2800 axiom entries).

The older manuscript proof outline also needs to be aligned with the checked
half-square induction and interior column reversal. Historical paired-child
and no-wrap proof-search notes are retained as provenance, not an active agenda.
The aggregate theorem does not prove their unused auxiliary claims.

No new examples or general symmetric-functions library are planned. Current
ownership and verification logs are recorded in [HANDOFF](../HANDOFF.md).

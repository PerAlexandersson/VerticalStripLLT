# Ground candidate defect reports in current source

A build-free review of `GainLevels.lean` initially reported a defect by quoting
code from the different `GainSlack` strategy. Rereading the actual file showed
that the fixed upward-edge pivot was correct; the reviewer retracted the claim.

For future reviews, require the current path, declaration name and exact source
snippet for every proposed defect. Compare against current ownership and build
status before making a repair. A compiled theorem can still have a wrong
statement, so compilation supplements rather than replaces semantic review.

This is a workflow proposal, not a change to agent policy.

For recurrence proof search, also require an actual source component before
treating a coefficient pattern as an obstruction. A proposed NN relay failure
on an eleven-state target tree component disappeared once its coefficients
were computed from source-component indicators. An arbitrary assignment of
piece weights need not occur in the recurrence. Record the diagram, corner,
source component and nonzero boundary coefficients before investigating such
a proposed obstruction; then seek a uniform repair for the realized pattern.

# Ground candidate defect reports in current source

A build-free review of `GainLevels.lean` initially reported a defect by quoting
code from the different `GainSlack` strategy. Rereading the actual file showed
that the fixed upward-edge pivot was correct; the reviewer retracted the claim.

For future reviews, require the current path, declaration name and exact source
snippet for every proposed defect. Compare against current ownership and build
status before making a repair. A compiled theorem can still have a wrong
statement, so compilation supplements rather than replaces semantic review.

This is a workflow proposal, not a change to agent policy.

# Keep verification logs tied to source checkpoints

The working name axioms-4.log was reused for a later inventory (856 queries
became 860). Earlier documentation still named that file, and concurrent
review could no longer recover its earlier contents from the path alone.

Suggestion: after each successful audit, retain a copy named for the source
commit, and record its query count and SHA256 digest alongside that commit.
Continue using a short working log name while iterating. The 77cabb9 audit
already has such a copy. This is a workflow proposal, not a new build rule.

# Check standalone proof-request packaging

The circular reachability request had an extra namespace closing line after
flattening a checked module. Aristotle repaired the scope and supplied a proof
that passed locally, but reported `COMPLETE_WITH_ERRORS` for the request.

Proposed improvement: centralize the existing source-flattening procedure in a
small project script that records module order, exact target text, and namespace
boundaries. Before submission, parse/check the packaged target with the sole
serialized `lake-workspace` owner. Keep payloads and results in the external
request directory. Compare returned definitions and target statements before
porting proofs. This is a tooling proposal, not an additional approval rule.

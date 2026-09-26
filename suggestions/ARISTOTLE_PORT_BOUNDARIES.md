Aristotle proof extraction currently relies on flattened source markers and
manual line ranges. One returned port ended halfway through the final theorem;
local verification caught it before commit. Flattening also causes private-name
collisions and repeats Lean 4.28/4.34 proof-script compatibility repairs.

Suggested improvement: use a reusable external-cache request packager that
records full module hashes and extracts appended modules by named boundaries,
then checks namespace balance and the exact final theorem tail before review.
Keep source definitions and statement hashes fixed; compatibility changes should
remain explicit proof-script-only changes. Do not automatically import the
service's rewritten prefix. Reuse existing workspace packaging tooling if one
is available before adding a new script.

# Reusable flip enumeration

The companion-lemma research now uses the same finite circular flip enumerator
for several bounded certificates. Rust already supplies the authoritative HRV
calculation, but no public selected-edge cover/flip/component API was found in
the capability audit. Python currently supplies only the external exploratory
enumeration and orchestration. A reviewed bounded Rust BFS probe now lives
externally at `diamond-exploration/hrv-bridge/src/bin/component_source_probe.rs`.
It is a candidate implementation, not a maintained API: cross-checks and
source hashes are recorded in `docs/proofs/COMPONENT_SOURCE_BRANCHING.md`.

Before extending this into a continuing search tool, coordinate ownership with
the Rust project and move the stable lifted-cover and complete-component
enumeration into the narrowest owning combinatorics/LLT crate. Retain tests for
periodic cover alternatives, strict long edges, empty admissible sets, and the
two independently checked locality obstructions. This is a pending integration
task, not authorization to edit another project's active source lane.

The refreshed read-only audit found the earlier ordinary implementation at
`/workspace/rust/experiments/src/bin/llt_flip_components.rs`, with private
`flip_component`, `llt_flip_neighbors`, `is_llt_flip_pair`, and
`component_generating_function`. Reuse its tested ideas when promoting an API,
but check ordinary versus circular lifted covers explicitly. The maintained
`sym-poly/sym/src/llt.rs` supplies circular HRV and aggregate LLT routines;
`sym-poly/sym/tests/circular_hrv.rs` tests aggregate comparisons, not complete
flip-component formulas. The missing maintained boundary is still the circular
cover/flip/component enumerator and exact per-component comparison.

The 2026-09-28 recurrence search now also needs an export of complete flip
graphs and source/target component IDs for NN and DN moves. Include the small
counterexamples in `docs/proofs/COMPONENT_RECURRENCE_REDUCTION.md` when testing
that API: a correct graph enumerator must reproduce the unpruned collisions
as well as the corrected packet multiplicities. The current external probe
deduplicates diamond rows by linear list search, which limits larger scans;
use keyed edge/row sets in the maintained implementation. This remains a
proposal requiring Rust ownership coordination, not an instruction to build
another local enumeration engine.

The direct NN driver now also repeatedly combines this graph model with the
maintained strict P-partition, HRV and sparse linear-algebra APIs. Preserve
the positive integral certificates in `COMPONENT_NN_REDISTRIBUTION.md` and
the saturated eight-state counterexample in `COMPONENT_NN_OVERLAPS.md` as
regression fixtures during integration. The latter is especially useful:
its HRV cancellation passes while its coloring cancellation fails by 42.
The stable graph/certificate interface should move into the maintained Rust
library after ownership coordination; keep research-specific coefficient
search and presentation in an external consumer. Current frozen driver and
receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/nn-overlap/`.

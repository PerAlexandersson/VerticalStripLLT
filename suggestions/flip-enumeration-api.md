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

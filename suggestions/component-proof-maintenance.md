# Component proof maintenance

The completed component library still emits existing deprecated if-lemma and
unused-section-variable warnings. They do not affect the checked proofs, but
make real build diagnostics harder to spot. The first pass shortened MountainScan
and HRVScanExtraction by 41 lines and removed warnings in those two modules.
The second, Claude-audited pass removed 114 more lines across 13 modules and
extracted three shared helpers; see docs/PROOF_STREAMLINING.md. Further maintenance can
migrate deprecated local names in the remaining modules in small batches,
preserving public signatures and serialized builds. Unused section hypotheses
that appear in public signatures should not be silently removed.

Keep the literal HRV scan extraction and the forward-only circular component
transport as the default route. They avoid the larger ordered-partition bijection
and reverse flip transport that earlier plans would have required. The completion
audit records these decisions so future refactoring does not reopen that work.

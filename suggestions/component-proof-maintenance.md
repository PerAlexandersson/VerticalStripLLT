# Follow-up proposal: component proof maintenance

The completed component library still emits existing deprecated if-lemma and
unused-section-variable warnings. They do not affect the checked proofs, but
make real build diagnostics harder to spot. In a separate authorized maintenance
pass, migrate deprecated local names and trim unused section hypotheses in small
batches, preserving public theorem signatures and serialized builds.

Keep the literal HRV scan extraction and the forward-only circular component
transport as the default route. They avoid the larger ordered-partition bijection
and reverse flip transport that earlier plans would have required. The completion
audit records these decisions so future refactoring does not reopen that work.

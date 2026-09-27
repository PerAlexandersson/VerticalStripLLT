# VerticalStripLLT handoff

## Result and verification boundaries

Ordinary and full aggregate circular HRV expansion and e-positivity are
Lean-verified. The full ordinary flip-component formula has a complete
independently audited mathematical proof at pushed `2b9421e`; compatible
lifts give all balanced circular components. These component theorems are
not yet fully formalized. Primitive unbalanced circular components remain
open. The [proof status](docs/FLIP_COMPONENT_STATUS.md) and
[ordinary proof](docs/proofs/COMPONENT_ORDINARY_PROOF.md) are authoritative.

The prior aggregate verification checkpoint is `18fbb4d`: 1908 build jobs,
2037 axiom inventory entries with only `propext`, `Classical.choice` and
`Quot.sound`. The public circular declarations are
`coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`,
`coloringLLT_shifted_eq_orientation_sum`, and `coloringLLT_shifted_e_positive`
in `VerticalStripLLT.Circular`. They cover all valid diagrams and alphabets.
See [the circular completion audit](docs/CIRCULAR_COMPLETION.md).

Initialization commits `830cc6b`, `130f7e8` and the immutable references are
preserved. No shared Rust or Overleaf source changed in this continuation.

## Ownership and current Lean batch

Primary owns strategy, all integration, source changes and the sole global
Lean build slot. Only primary invokes `lake-workspace`; no slot transfer
occurred. Process checks found no competing batch build. The existing
RealRooted Lake serve/LSP processes remain untouched.

The user explicitly requested parallel Lean implementation. The modular
[plan](docs/COMPONENT_FORMALIZATION.md) was recorded and committed at
`683e4e7` before implementation delegation.

Luna returned two disjoint, build-free candidates and released ownership.
Primary reviewed and repaired their API/proof details, and now owns both:

- `VerticalStripLLT/Components/WordRelations.lean`: `WordModule`, `basisWord`,
  `fourWord`, `wordGenerators`, `wordRelations`, `WordQuotient`,
  `relations_le_ker`, `descend`, `descend_mk`, `quotient_eq_implies_eq`.
- `VerticalStripLLT/Components/WordContext.lean`: `contextMap`, `contextLinear`,
  `contextLinear_basisWord`, `contextLinear_fourWord`,
  `contextLinear_relations_comap`, `contextLinear_map_relations`,
  `contextQuotient`, `contextQuotient_mk`.

Namespace: `VerticalStripLLT.Components`. These are full general lemmas on
integer linear combinations of words. All contextual four-word relations
and all repeated-letter words are included. The quotient is additive;
no induced ring or completed component semantic bridge is claimed.

Primary owns `VerticalStripLLT.lean`, `Verification.lean`, this handoff, the
plan, index/status, Aristotle ledger and periodic proof note. No subagent
currently owns editable files. Astra and Terra completed read-only audits;
Astra also supplied the concrete existing-flip-graph plan for component counts.

## Active Aristotle request

Project `7e1e7b8f-b94d-4eef-86cf-51b2130269f5`, task
`44384423-1c84-42b4-a525-bba5b13212f3`, is IN PROGRESS. The native observer
is exec session `50488`. Do not restart the request if observation disconnects;
query this exact task. Primary owns monitoring and eventual integration as
`VerticalStripLLT/Components/WordConjugation.lean`.

The isolated request asks for inverse finite products, truncated conjugation,
and commutation with the sum of letters under squarefree and four-word
hypotheses. An optional iterated-commutator corollary is also allowed.
The service's cached Mathlib uses Lean 4.28.0. Primary explicitly allowed that
coherent remote environment for the candidate instead of rebuilding Mathlib;
all accepted code must still pass this project's pinned Lean 4.34.0 locally.
No returned theorem is yet accepted. The exact input hash and request details
are in [the Aristotle ledger](docs/ARISTOTLE.md).

External artifacts: `/lake-cache/ai-projects/requests/VerticalStripLLT/word-conjugation/`.
No prior Aristotle task remains active. The earlier mixed-corner and DN
returns supplied partial results only; their exact receipts and limitations
remain in the ledger, not in the current work queue.

## New circular companion results

The [periodic word audit](docs/proofs/COMPONENT_PERIODIC_WORDS.md) proves:

- the exact alternating coefficient formula for actual periodic lifted HRV
  maps, including why its local support conditions force projected acyclicity;
- positive- and zero-winding mixed-cycle map cancellation, with an exact
  negative-winding obstruction: distinct maps can cancel only after passing
  to their elementary fiber monomials;
- the corrected circular four-word count identity, retaining its four boundary
  terms. Even a saturated primitive singleton need not kill the ordinary
  relation. Backward circular edges also prevent reuse of the ordinary
  fixed-label coloring refinement unchanged.

Primary and Terra checked the coefficient theorem and winding distinction;
primary and Astra checked the count identity and singleton obstruction.
No computation or Lean build was used as a substitute for these proofs.
They are progress toward the remaining circular goal, not its completion.

## Checks and exact next steps

The integrated library build passed: `lake-workspace build VerticalStripLLT`,
1910 jobs. Only changed modules and their necessary dependents were rebuilt.
The axiom inventory audit passed (2017 entries listing dependencies),
with only the three standard axioms. Source guards, line widths, local links,
whitespace and both initialization-ancestor checks passed. Initial candidate elaboration
failures were fixed before the successful library build. Logs in the external
directory are `word-relations-build.log`, `word-context-build.log` (first
candidate failure), `word-library-build.log` (successful integrated build),
and `word-axioms.log`.

Next: push this coherent verified batch; monitor and locally verify
Aristotle's return. Then implement the actual
component-compatible-permutation pairing using `Circular.Orientation` and
`Circular.flipComponent` with a forward-edge hypothesis, as specified in
the committed plan. Induced multiplication, both semantic refinements and
finite Cauchy factorization remain necessary for the full Lean theorem.
Continue the primitive circular companion independently. The thread goal is
active: this turn makes mathematical and locally checked Lean progress.

Historical induction certificates remain valid alternative arguments, but
their stronger ordinary isolation problems are not prerequisites for the
new word proof. The [archived status](docs/archive/component-status-before-ordinary-word-proof.md)
and Git history retain earlier research chronology and exact obstructions.

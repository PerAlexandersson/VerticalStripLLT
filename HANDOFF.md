# VerticalStripLLT handoff

## Result and verification boundary

Current verified increment extends `948fbb4` / source `682b476` with five
modules: `CauchyStep`, `GainPotential`, `GainCancellation`, `GainSlack`, and
`SinkReachability`. The full library passed **1936 jobs**, and all **2206 axiom
inventory entries** passed with only `propext`, `Classical.choice`, and
`Quot.sound`. Source, width, whitespace and external-cache guards pass.
Logs are under `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`.
The goal remains active; subsequent candidates are still under development
as recorded in Ownership below.

`colorProduct_eq_cauchyProduct` now proves the finite ordered Cauchy
factorization. `GainData.potential_feasible` constructs the least potential
from feasibility, and `potential_erase_eq` proves strictly slack deletion
invariance. `sum_powerset_feasible_eq_zero` proves the resulting signed
feasibility cancellation using the actual canonical-potential pivot.
Feasibility from closed-walk inequalities, positive-excess slack, scalar
extension and the actual forward HRV fiber bridge are the next increment.

The ordinary actual-component word-count milestone is now formalized:
`Components.componentWordCount_four` proves the contextual four-term identity
under the ordinary forward-edge hypothesis, and `componentWordFunctional`
descends the guarded count to the integer-linear word quotient. The proof uses
actual directed flips within the original complete component, covers invalid
words and absent long edges, and permits the retained long edge to be strict.
This completes the former full-word/flip-bijection integration milestone.
Final validation: the complete library passed 1931 jobs and all 2169 axiom
inventory entries passed, using only `propext`, `Classical.choice`, and
`Quot.sound`. All 71 public declarations added during this restart are
inventoried. Source, 100-column, whitespace, 44 local-link, and external-cache
guards passed. Final logs are `final-library-build.log` and `final-axioms.log`
under `/lake-cache/ai-projects/requests/VerticalStripLLT/component-words/`.

The requested finite companion lemma now has a COMPLETE mathematical proof,
including isolation of entire circular flip components. See
[the corrected proof](docs/proofs/COMPONENT_FINITE_COMPANION.md).
Aristotle supplied the canonical coefficient recurrence; primary and Astra
independently audited all steps, and Terra checked the ordered-partition
identity and reindexing. Primary supplied an explicitly finite component
reconstruction; Astra audited its covers, gains, signs and period handling.

The proof uses a signed ordered-partition identity, canonical integer
longest-path potentials after scaling, a strict-slack edge involution, and
induction on edge count. The final flip reconstruction preserves the original
component and gives identical contracted gain graphs. It uses no polyhedral,
topological or unproved confluence theorem. One unused false sentence about
unscaled integer strict potentials was removed from the returned candidate;
the scaled construction correctly gives rational strict potentials.

The full ordinary and circular COMPONENT theorems are not yet Lean theorems.
Their mathematical proofs are complete. The full ordinary and aggregate
circular HRV formulas and e-positivity remain locally Lean-verified; see
[ordinary completion](docs/COMPLETION.md) and
[circular completion](docs/CIRCULAR_COMPLETION.md).

## Ownership and current checkpoint

Active goal continuation: formalize the **full circular component proof**.
The preceding turn is classified as verified progress, not completion of this
goal. Starting checkpoint is clean `948fbb4` / source `682b476`.
Primary now owns new `Components/GainPotential.lean` and `Components/GainSlack.lean`, the returned Luna
candidates `Components/SinkReachability.lean` and `Components/GainCancellation.lean`,
plus integration, imports, inventory and documentation. Luna `word_swaps` now
audits the actual HRV semantic bridge; Luna `word_covers` audits available
difference-constraint APIs (both read-only). Astra's returned
`Components/CauchyStep.lean` candidate is now primary-owned for integration.
Luna `word_covers` returned `Components/GainExcess.lean`; primary adopted it
for validation, and that subagent is now idle and build-free.
Astra `component_review` next owns only new `Components/GainFeasibility.lean`.
Luna `word_swaps` next owns only new `Components/WordScalars.lean`.
Primary also owns new `Components/ForwardHRV.lean` for actual circular HRV
fibers under the ordinary forward-edge hypothesis.
All delegated work is build-free, and primary
retains the sole serialized Lean build slot. No account or worker launch change.

The explicitly requested academic-account restart on 2026-09-27 resumes the
same primary ownership in `/workspace/lean/VerticalStripLLT` on `main`, from
clean, pushed checkpoint `5dd1d2a`. The user subsequently explicitly authorized
Luna subagents and Astra for formalization. Primary owns `Components/ComponentWords.lean`,
the root import, verification inventory, and accompanying status documents.
The resumed increment proves full-word counts, the actual four-term flip
bijection and the resulting ordinary component quotient functional.
The runtime Lean MCP is still rooted in RealRooted; use the existing explicit
source-search / `lake-workspace` fallback described in
`suggestions/project-tool-routing.md`. Check processes before each build.

Ownership (2026-09-27): primary owns all integrated modules, imports,
inventory, documentation and the sole Lean build slot. Both Luna subagents
(`word_swaps`, `word_covers`) and Astra (`component_review`) have returned all
assignments and released editable ownership. All were build-free; no build
slot was transferred. Primary compiled and repaired every candidate before
integration. Luna independently audited the final bijection and functional,
including no-edge and invalid-word cases, with no material issues found.

Independent Astra review decision: construct target admissibility directly
with the forward numeric coloring (`EdgeData.lt_of_transGen`), then use the
selected-edge exchange identity for word compatibility and a finite conditional
bijection for filtered counts. The existing component and full integer cover
relations are retained. The completed finite companion audit is not repeated.

Restart checkpoint verification: `ComponentWords` passed its focused build
(1411 jobs), the root library passed 1920 jobs, and the expanded axiom inventory
passed 2116 entries with only `propext`, `Classical.choice`, and `Quot.sound`.
All 18 new declarations are inventoried. Source/100-column/whitespace guards,
37 local documentation links, and absence of local package/build trees passed.
Logs: `/lake-cache/ai-projects/requests/VerticalStripLLT/component-words/`.
The first compile exposed an ordinary/circular `Orientation` name collision;
explicit qualification fixed it. SSH fetch failed for lack of a loaded key;
fetch over HTTPS using the existing `gh` credential helper succeeded without
changing remotes, stored configuration, or accounts.
The verified full-word checkpoint is committed and pushed as `de4645f`.
The verified local-flip checkpoint is committed and pushed as `06fac39`.

The local flip integration now passes the complete library build (1929 jobs)
and 2164 axiom inventory entries, with only the three standard axioms.
All 66 declarations added since the restart are inventoried; source, width,
whitespace, 37 local-link and external-cache guards passed. Logs are
`local-flip-library-build.log` and `local-flip-axioms.log` in the directory above.
The `WordCover` candidate commits `4eed223`/`807114e` are adopted into this
verified increment with canonical-residue and implicit-argument corrections.
Two harmless unused-hypothesis linter warnings remain in the generic word
exchanges; signatures are retained. The count reduction still has an explicit
filtered-cardinality premise. `ComponentBijection` now discharges that premise
for natural long edges; `ComponentFunctional` handles absent long edges and
invalid words, then proves quotient descent without any cardinality premise.

Earlier word-ring and companion checkpoints are `3dcb0f8` and `5dd1d2a`.
Their remote proof requests and worker assignments are terminal. No Rust,
Overleaf, reference source or shared infrastructure was changed.

Initialization commits `830cc6b` and `130f7e8` remain ancestors. The immutable
paper references remain untouched. Overleaf v9 remains unchanged at SHA-256
`3b02859804569cf17a9fc037bd69390fc1afae2265cff559c752369ef05c9195`.

## Exact integrated declarations

Paths below are under `VerticalStripLLT/Components/`. Unless stated otherwise,
the namespace is `VerticalStripLLT.Components`.

- `WordRelations` and `WordContext`: additive contextual quotient, universal
  functional descent, and preservation by prefix/suffix contexts; pushed at
  `a8ebd20`.
- `WordConjugation`: inverse finite products, `descendingProduct_conj`,
  `letterSum_commute_descendingProduct`, and `descendingProduct_conj_adPow`;
  locally checked Aristotle candidate, pushed at `6b7cd80`.
- `WordMultiplication`: `wordCoefficients_context`,
  `wordRelations_left_mul`, `wordRelations_right_mul`.
- `WordAlgebra`: genuine ring quotient and `wordAlgebraEquiv`, a linear
  equivalence to the original additive quotient; `wordProjection_eq_iff`
  proves that exactly the original relations are imposed.
- `WordGenerators`: `algebraWord_sandwich` and `algebraWord_triple` discharge
  the concrete generator hypotheses of the conjugation module.
- `BlockExtractor`: `blockWord_compatible_iff_forall_sink`.
- `BlockCancellation`: `blockCancellation`, `blockCancellation_erase`, and
  `blockCancellation_uniqueSink`, for arbitrary finite increasing graphs.
- `WordRank`: `wordCompatible_idxOf_lt` and `idxOf_middle`.
- `LiftCoverRank`, namespace `Circular.Diagram`: `rank_lt_of_liftReach`,
  `liftCover_of_liftStep_rank_gap`, `liftCover_of_liftStep_rank_succ`.
  These use the ACTUAL full integer cover relation; no no-wrap hypothesis.
- `ComponentWords`: guarded counts in the actual flip component, their linear
  extension, repeated-word vanishing, component invariance and strict ranks.
- `ShortEdges`: normal short-edge construction and canonical forward lifts;
  `EdgeSwap`: exact selected-relation exchange and its inverse.
- `WordSwap`, `WordSwapInverse`, `WordNeutral`: compatibility of exchanged and
  unchanged triples, plus permutation invariance of full-word guards.
- `WordCover`: all four covers of contiguous `acb`/`bac` words.
- `WordFlip`: `directedFlipWitness_of_compatible_triples` derives every cover
  field and supplies actual component closure.
- `ComponentSwap`: deterministic exchanged orientations and compatible forward
  and backward actual flips, including the case of a strict retained long edge.
- `CountReduction`: reduces the four-term count identity to the cardinality
  equality of the selected-long-edge filters.
- `ComponentBijection`: `selectedLong_card_eq_of_naturalLift`, the conditional
  actual-component bijection satisfying that cardinality premise.
- `ComponentFunctional`: `componentWordCount_four`,
  `componentWordLinear_relations_le_ker`, `componentWordFunctional`, and
  `componentWordFunctional_mk_basisWord`. The public count theorem has no
  full-word, selected-edge, cover or cardinality premise; it assumes the
  ordinary forward-edge condition and `a < b < c`.

These are full general ingredients, not examples or declarations of the
complete component theorem. The component functional remains linear rather
than a ring homomorphism.

## Checks of the pre-restart companion checkpoint

The combined `lake-workspace build VerticalStripLLT` passed **1919 jobs**.
`lake-workspace env lean Verification.lean` passed **2098 inventory entries**,
using only `propext`, `Classical.choice`, and `Quot.sound`. The local versions
are Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
No placeholders, custom axioms or unchecked native proofs are permitted.
All ten component modules passed source and 100-column guards; 119 local
link targets, whitespace, initialization ancestry and unchanged references
were checked. No project-local package or build output was created.

Logs under `/lake-cache/ai-projects/requests/VerticalStripLLT/word-algebra/`:
`block-build.log`, `rank-build.log` (initial WordRank API failure),
`word-rank-build.log` (corrected success), `library-build.log`, `axioms.log`.
AXLE independently accepted the complete block files in `lean-4.34.0`, request
`c2652d3c-f8d2-4088-9c22-dc377ca51674`, with no warnings or failed declarations;
its full input/output is `block-axle-final.json` in that directory.

An initial one-second BlockExtractor check briefly overlapped a newly started
RealRooted build because inspection and launch were mistakenly batched before
reading process output. We then paused all local builds until PID `3703098`
finished. Subsequent RealRooted batches `3720768` and `3723625` also finished
before our remaining checks. Native waiters ended. All later process checks
and build launches were separate decisions. Existing RealRooted editor/LSP
processes were left untouched. A shared-lock proposal is recorded in
[suggestions](suggestions/shared-lean-build-lock.md); no wrapper was changed.

## Aristotle result and provenance

Finite coefficient project `729ff94c-1911-422b-88a7-f1af1cef93d0`, task
`91a37895-7b0f-420d-aa72-92da80540500`, is terminal **COMPLETE_WITH_ERRORS**.
It returned a complete prose proof, not a Lean formalization. Acceptance is
based on the independent mathematical audits and correction above, not the
service status. Original inputs, output archive and returned proof remain in
external `circular-finite-coefficients/`; exact hashes and review findings are
in [the ledger](docs/ARISTOTLE.md). Earlier observer connection errors did not
trigger a replacement task. All relevant Aristotle tasks are terminal.

The Overleaf v9 bounded-face proof remains an independently audited reference.
The [comparison](docs/proofs/COMPONENT_CIRCULAR_FACE_PROOF.md) records the
ordinary simplification and the direct cycle-deletion input. No manuscript
source was edited by this task.

## Remaining Lean work

The proof-discovery objective is satisfied by the finite companion and its
whole-component reconstruction. Full Lean integration is a separate remaining
milestone, detailed in [the modular plan](docs/COMPONENT_FORMALIZATION.md):

1. Prove the strict-coloring refinement and finite Cauchy factorization paired
   with the now-verified `componentWordFunctional`.
2. Assemble the global HRV extraction from the local block cancellation, then
   transport entire balanced components via compatible lifts.
3. Formalize the ordered-partition identity, scaled canonical potentials,
   coefficient recurrence, edge-count induction and finite tight-flip
   reconstruction. Ordered partitions may be surjective maps V→Fin k,
   allowing k=0 for the empty vertex set.

No remaining mathematical gap is asserted for the companion. The unfinished
Lean milestones must not be reported as already formalized.

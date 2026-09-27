# VerticalStripLLT handoff

## Current result and verification boundary

Active goal: **formalize the full circular component proof**, with ordinary
component assembly proceeding in tandem at the user's explicit request.
The complete ordinary and aggregate circular formulas are Lean theorems.
The full ordinary and circular **component** formulas have complete audited
mathematical proofs but are **not yet complete Lean theorems**.

Verified full partition/coefficient increment atop pushed `e63e21b`:
`PartitionConnectivity.signedSum_eq_weakComponentCount` completes Lemma A;
`GainCoefficientCancellation.sum_powerset_cyclicNegative_eq_zero_of_gain_excess`
proves abstract (**′**). Astra independently audited actual source and found
no defect; optional support, edge multiplicities, repetitions and signs are explicit.
Full library: **1987 jobs**, **2382 axiom entries**, standard axioms only.
Earlier pushed checkpoints: `ee8eb02` (actual color-product pairing and negative-cycle
cancellation), `e63e21b` (DAG partition evaluation, level cancellation, HRV blocks).

Validation logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`:
`coefficient-library-build.log` and `coefficient-axioms.log`.
All builds use the pinned Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` through `lake-workspace`.
No placeholders, custom axioms, unchecked native proofs or local package/build
output are allowed. The expected axioms are only `propext`, `Classical.choice`,
and `Quot.sound`.

## Ownership

The academic-account restart continues in the assigned main checkout
`/workspace/lean/VerticalStripLLT`, branch `main`. Primary owns all integrated
source, imports, inventory, documentation, integration fixes and the sole
serialized Lean build slot. Check active processes before each build.
Primary additionally owns `Components/ColorProductPairing.lean`, the ordinary
product/subword reindexing and strict-enumerator pairing (now verified), and
`Components/GainLevels.lean`, level-compatible edge insertion and cancellation,
and `Components/SquarefreeProducts.lean`, repeated-index product vanishing.
Primary also owns `Components/PartitionLevels.lean`, the actual partition-level adapter,
and `Components/GainCoefficientCancellation.lean`, signed partition/coefficient cancellation.

Current authorized build-free assignments:

- Astra `component_review`: only `Components/GainContraction.lean`, balanced
  potentials, weak-block contraction retaining edge instances, potential differences.
- Luna `word_covers`: only `Components/MountainExpansion.lean`, remove overlap
  and identify adPow with the ordered signed mountain-subset sum.
- Luna returned `Components/MountainSubsetCoefficients.lean`; primary owns validation.
- All other candidate files were returned and integrated by primary. No build
  slot was transferred. Luna's subword filter length lemma needed an explicit
  nodup premise; primary added it before successful compilation.

All earlier candidate files were returned and adopted by primary. No build
slot was transferred. No new account, supervisor worker or worktree was started.
The user allows several Luna subagents and Astra, with optional Claude advice.

The runtime Lean MCP remains rooted in RealRooted. Explicit source search and
serialized `lake-workspace` are the recorded fallback; see
[suggestions/project-tool-routing.md](suggestions/project-tool-routing.md).
`codex mcp list` and runtime registry discovery were performed this continuation.
Git SSH has no loaded key. Routine pushes use the existing gh credential helper
with command-local HTTPS rewriting, without changing remotes or stored config:

```sh
git -c url.https://github.com/.insteadOf=git@github.com: \
  -c credential.helper='!gh auth git-credential' push origin main
```

Integrated verified source includes the partition condensation/connectivity and
level adapters, abstract gain coefficient cancellation, overlap vanishing and
subset reindexing ingredients. Full contracted per-F and W recurrence bridges
remain open. A false-positive Luna audit conflated GainLevels with GainSlack;
it was explicitly retracted after rereading current source. See the review-grounding suggestion.

## Verified component foundations

All paths below are under `VerticalStripLLT/Components/`.

- `ComponentFunctional.componentWordCount_four` proves the contextual four-term
  count identity inside the original complete flip component under the ordinary
  forward-edge hypothesis. It handles invalid words, missing natural long
  edges, and strict retained long edges. `componentWordFunctional` is its
  integer-linear quotient descent. Source checkpoint `682b476`.
- `WordAlgebra`, `WordGenerators` and `WordConjugation` give the exact ring
  quotient, squarefree and triple relations, and finite conjugation identities.
- `CauchyStep.colorProduct_eq_cauchyProduct` proves the finite ordered Cauchy
  factorization. Colors and peak factors retain their multiplication order.
- `WordScalars` and `FiniteWordCauchy` instantiate this identity over a scalar
  tensor algebra. `ElementaryScalars` identifies the finite coefficients with
  Mathlib elementary polynomials and proves transport along ring maps.
  `ComponentScalars.componentScalarEval` remains linear; no multiplicativity
  of the actual component functional is assumed.
- `CommutatorCoefficients.inverseConjugationPolynomial_coeff` proves the signed
  inverse-conjugation coefficient formula. This is the coefficient half of
  equation (4), not yet the full ordered-subset mountain expansion.
- `WordProductExpansion` expands ordered products into weighted subwords and
  evaluates them through the actual component functional.
- `ColorProductPairing.componentScalarEval_colorProduct` identifies the actual
  component strict enumerator with the finite color-product pairing.
  `componentScalarEval_cauchyProduct` transfers this via the ordered Cauchy identity.
  `ColoringSubwords` and `ColorProductPositions` prove full-subword/coloring
  bijectivity, weights and ordering, including empty cases.
- `PartitionCondensation` transports the actual finite partition sum to the
  strong-component quotient. `PartitionConnectivity.signedSum_eq_weakComponentCount`
  completes Lemma A, including loops and isolated vertices.
- `PartitionLevels` relates this enumeration to finite level assignments.
  `GainCoefficientCancellation.sum_powerset_cyclicNegative_eq_zero_of_gain_excess`
  proves the abstract (**′**) sign (-1)^(|J|+c(A∪J)). Astra independently audited
  current source: no defect, exact optional support/repetitions preserved. This
  does not yet instantiate actual balanced-F contractions or prove W's recurrence.
- `OrderedPartitions` enumerates actual compatible nonempty top-first blocks,
  proves completeness and the signed top-block recursion. `OrderedPartitionDAG`
  evaluates their actual signed sum for every acyclic relation, including empty sets.
- `GainLevels` proves the fixed-level alternating sum vanishes, using an upward
  edge toggle or endpoint balance and negative-cycle cancellation. Optional
  edge support is explicit; no strong-connectivity shortcut is assumed.
- `ConjugationSubwords` and `MountainCoefficients` give the exact signed double
  subword coefficient formula; overlap removal and support reindexing remain.
- `MountainWords` connects maximum-insertion mountain notation to block cancellation.
  `HRVPartition` identifies qualifying ordered blocks with the actual HRV fibers.
- `GainScaling` proves the finite strict-scaling equivalence.
  `GainNegativeCancellation` proves the alternating negative-simple-cycle sum
  vanishes under the explicit balanced endpoints and positive gain excess.
- `ColoringWord.wordCompatible_coloringWord_iff` proves that the full word formed
  by increasing colors and decreasing ties is compatible exactly for strict
  selected-edge colorings. `ComponentColoring.componentStrictEnumerator_eq_coloringWord_sum`
  gives the direct refinement of the actual complete component enumerator.
- `SinkReachability` proves the finite unique-sink/reachability equivalence.
  `ForwardHRV.hrvFiber_blockCancellation_forward` (in namespace
  `Circular.Orientation`) applies local cancellation to actual circular HRV
  fibers under the ordinary forward-edge hypothesis. Numeric maximality is
  derived from the existing lifted HRV, not a replacement definition.
- `GainPotential` proves least-potential feasibility and invariance under
  inserting satisfied constraints or deleting strictly slack constraints.
  `GainSlack` derives signed feasibility cancellation using its actual pivot.
- `GainFeasibility.exists_feasible_iff_closedWalksNonpos` proves the full finite
  difference-constraint criterion. `GainExcess` supplies slack from a positive
  signed gain excess and derives the signed closed-walk recurrence. Edge
  instances, loops, parallel edges and repeated walk steps are retained.

Astra independently reviewed the tensor representation, multiplication order,
coefficient signs and linear functional boundary: no defect found. Luna
independently reviewed the gain/potential and actual HRV bridges: no defect
found. Primary repaired and locally built all candidates. The generic gain
recurrence now has its strict-scaled form; actual contracted graphs remain to be instantiated.

## Remaining assembly

Ordinary track:

1. The finite product/coloring pairing is complete in `ColorProductPairing`.
2. Remove overlapping terms and reindex the verified ordered double-subword
   coefficient sum into signed mountain blocks. `MountainWords` has the local
   cancellation form and `HRVPartition` identifies qualifying ordered blocks
   as actual HRV fibers; the weighted global sum still needs assembly.
3. Apply the same linear functional to the two sides of Cauchy to export the full
   ordinary component theorem; transport entire balanced components by compatible lifts.

Circular track:

1. Scaling and negative-cycle cancellation (Lemma X) are complete in
   `GainScaling` and `GainNegativeCancellation`.
2. The full signed ordered-partition identity and abstract gain coefficient
   cancellation (**′**) now compile; Astra independently audited them. Apply them
   to each actual balanced-F contraction: potential independence, weak-component
   preservation, excess transport, optional-subset reindexing and constant signs.
3. Supply the balanced base case, an excess/deletion witness for each unbalanced
   set, the actual signed deletion recurrence for W, and edge-count induction.
4. Integrate finite tight-edge flip reconstruction and prove whole-component
   isolation using identical contracted gain graphs.

These are remaining Lean obligations, not remaining mathematical conjectures.
Do not infer component positivity from an aggregate theorem.

## Proof sources and history

Preferred source: [finite circular companion](docs/proofs/COMPONENT_FINITE_COMPANION.md).
Ordinary source: [ordinary component proof](docs/proofs/COMPONENT_ORDINARY_PROOF.md).
[The integration plan](docs/COMPONENT_FORMALIZATION.md) records module correspondence.
The companion was independently audited by primary and Astra, with Terra
checking its partition identity. The proof uses finite sums, potentials and
flip reconstruction; general polyhedral machinery is unnecessary.

Aristotle finite coefficient project `729ff94c-1911-422b-88a7-f1af1cef93d0`, task
`91a37895-7b0f-420d-aa72-92da80540500`, is terminal `COMPLETE_WITH_ERRORS` and
returned prose, not Lean. The corrected proof was accepted after independent
audits, not from the service status. See [the ledger](docs/ARISTOTLE.md).
All other old Aristotle tasks are terminal.

Earlier checkpoints, exact audit provenance, build history and ownership are
preserved in [the archived handoff](docs/archive/component-foundation-through-cauchy-20260927.md).
No Rust, Overleaf, immutable references or shared infrastructure was changed.

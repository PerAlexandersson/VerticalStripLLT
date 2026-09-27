# Historical handoff through tight circular flips

Snapshot only. Current HANDOFF.md controls ownership and resume state.

# VerticalStripLLT handoff

## Current result and verification boundary

Active goal: **formalize the full circular component proof**, with ordinary
component assembly proceeding in tandem at the user's explicit request.
The complete ordinary and aggregate circular formulas are Lean theorems.
The full ordinary and circular **component** formulas have complete audited
mathematical proofs but are **not yet complete Lean theorems**.

Verified finite companion checkpoint `6bf5f42` is pushed. The current tight-flip
increment compiles in focused checks: scaled tight potentials, score-based
full-cover preservation, actual triangle extraction, balancedness across flips,
contracted coefficient transport, and the coefficient-preserving forward
ambient extension inside the original component. Independent source review
found no material defect. Ordinary ordered-block HRV and flattened compatibility
adapters also compile. Full library passes **2029 jobs**, with **2578 axiom
entries**, only standard axioms, and passing source/line-width/diff guards.
The inverse extension and coefficient-sum bijection remain under construction.

Earlier pushed checkpoints: `f668154` (mountain equation (4) and potential
independence; 1992 jobs, 2416 axioms), `b60d299` (Lemma A and abstract (**′**)),
`ee8eb02` (actual color-product pairing), `e63e21b` (DAG/level/HRV blocks).
Validation logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`:
`finite-companion-library-build.log` and `finite-companion-axioms.log`
(2017 jobs, 2529 axioms); next logs are `tight-flip-library-build.log` and
`tight-flip-axioms.log`.
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
Current authorized build-free assignments:

- Astra `component_review`: released TightFlipInverse candidate; primary is
  validating it separately from the forward-extension checkpoint.
- Luna `word_covers`: owns only `Components/BlockFullWords.lean`, the full-word
  carrier/partition adapter. Build-free.
- Luna `word_swaps`: completed read-only audit of score, cover and balanced-flip
  modules; no material defect found. Idle, no edit ownership.

All earlier candidates were returned, repaired where needed, and checked by
primary. No build slot was transferred. No new account, supervisor worker or
worktree was started. The user allows several Luna subagents and Astra, with
optional Claude advice. Completed ownership history is archived below.

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

The actual per-F coefficient recurrence, semantic W recurrences and finite
companion induction are now verified. Whole-component bridges remain open;
they are not inferred from aggregate positivity. A false-positive Luna audit conflating GainLevels with
GainSlack was explicitly retracted; see the review-grounding suggestion.

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
  inverse-conjugation coefficient formula. `MountainExpansion.adPow_mountain_expand` now proves the full signed
  ordered-subset mountain expansion in equation (4).
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
  current source: no defect, exact optional support/repetitions preserved. Actual balanced-F instantiation is now verified in
  `GainCoefficientRecurrence`; both semantic W recurrences are now verified.
- `OrderedPartitions` enumerates actual compatible nonempty top-first blocks,
  proves completeness and the signed top-block recursion. `OrderedPartitionDAG`
  evaluates their actual signed sum for every acyclic relation, including empty sets.
- `GainLevels` proves the fixed-level alternating sum vanishes, using an upward
  edge toggle or endpoint balance and negative-cycle cancellation. Optional
  edge support is explicit; no strong-connectivity shortcut is assumed.
- `ConjugationSubwords` and `MountainCoefficients` give the exact signed double
  subword coefficient formula. `MountainSubsetCoefficients` and `MountainExpansion`
  complete overlap removal, support reindexing and the signed mountain expansion.
- `GainContraction` retains original edge instances while contracting balanced blocks.
  `GainGauge` and `GainContractionGauge` prove potential independence of cycle tests.
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
recurrence, actual contracted coefficient recurrence and both semantic W
recurrences are verified.

## Remaining assembly

Ordinary track:

1. The finite product/coloring pairing is complete in `ColorProductPairing`.
2. The ordered double-subword coefficient sum has been reindexed into signed
   mountain blocks, with overlapping terms removed. `MountainWords` has the local
   cancellation form and `HRVPartition` identifies qualifying ordered blocks
   as actual HRV fibers; the weighted global sum still needs assembly.
3. Apply the same linear functional to the two sides of Cauchy to export the full
   ordinary component theorem; transport entire balanced components by compatible lifts.

Circular track:

1. Scaling and negative-cycle cancellation (Lemma X) are complete in
   `GainScaling` and `GainNegativeCancellation`.
2. The full partition identity, actual coefficient recurrence (**), balanced base,
   potential independence and all contraction transports are complete.
3. The excess/deletion witness, both actual signed W recurrences and finite-set
   induction are complete in the per-orientation finite companion.
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

Latest ownership and verification chronology is in
[the coefficient checkpoint archive](docs/archive/component-foundation-through-coefficients-20260927.md).

Latest finite-companion ownership chronology is archived in
[the finite companion snapshot](docs/archive/component-foundation-through-finite-companion-20260927.md).

## Next concrete work

The per-orientation finite companion, tight-path cover reconstruction and
forward coefficient-preserving ambient extension are complete. Integrate the
inverse extension, prove the coefficient-sum bijection/constancy on balanced
components, then compatible-lift transport. Astra recommends transporting contracted graphs by
an equality of the underlying EqvGen setoids, avoiding a new quiver-cast layer.
The ordinary lane still needs global ordered mountain-product HRV extraction;
`AncestorBlock` now identifies the incoming-closed block with its ancestor set.
Both full component theorems remain open. Primary retains the single build slot.

Primary owns `Components/TightReachability.lean` and
`Components/CircularTightPaths.lean`: monotone-score path restriction and actual
lifted-cover preservation. These are the next finite component-isolation steps.

Astra reviewed the next architecture: retain weakBlock quotients and transport
by equality of EqvGen setoids. No quiver-path transport layer is needed. The
same-area undecorated adapter only preserves individual semantics, not entire
components; universal-ambient component preservation remains an explicit gap.
Astra component_review now owns only `Components/GainCoefficientTransport.lean`,
implementing the quotientGain/setoid transport and coefficient equality for a
common potential, equal weak closures, and equal residual selected edges.
Build-free; primary retains all other sources and builds.

Luna word_swaps now owns only `Components/GainTriangleSwap.lean`, a generic
edge-triangle swap preserving all balanced-potential equations and weak
connectivity under explicit endpoint/length identities and retained long edge.
Primary adopted the compiled GainTightPotential candidate. Build ownership unchanged.

Luna word_covers now owns only `Components/OrderedBlockHRV.lean`, deriving
no-backward cross-block compatibility from the existing reversed-relation
ordered partitions and constructing the owner map for HRVPartition. This is a
bounded ordinary semantic adapter; it does not claim the global product sum.
Build-free; all other ownership unchanged.
Primary owns `Components/FlipTriangle.lean`: extract the actual retained long
edge and endpoint/length identities from DirectedFlipWitness without no-wrap
assumptions. This will connect the generic triangle swap to circular flips.
Primary adopts released GainCoefficientTransport and OrderedBlockHRV candidates.
Primary owns `Components/TightFlipReconstruction.lean`, lifting an existing
flip witness through tight selections and constructing the exchanged ambient
orientation using positive scaled potentials. All builds remain serialized.
All returned modules are primary-owned. Astra component_review owns only
`Components/TightFlipExistence.lean`, constructing the ambient exchanged
orientation and lifted witness from an explicit positive scaled tight potential.
It may use the compiled TightFlipReconstruction.of_tightSelections API; no
builds or edits elsewhere. Primary owns actual balanced-flip/coefficient adapters.
Luna word_covers owns only `Components/BlockWordSupport.lean`: membership of a
blockWord is its block when the tail subset lies inside, and compatibility of
a flattened family is exactly internal compatibility plus block-level cross
compatibility. This is a build-free ordinary local adapter.
Primary owns `Components/CircularBalancedFlip.lean`: actual balancedness and
weak-connectivity preservation along circular flips, plus companion coefficient
transport for an ambient exchange with matching residual selected edges.
Astra released TightFlipExistence; primary adopts it. Astra now owns only
`Components/TightFlipInverse.lean`, constructing the source ambient orientation
from a target-tight selection for the same directed witness (not reversing the
witness). This supplies the inverse direction required for the coefficient
bijection. No builds or other edits are authorized.
Primary owns `Components/CircularGoodFlip.lean`, assembling tight extension
with actual coefficient equality and complete-component membership. The reverse
extension is still Astra-owned until returned.
Luna word_covers returned BlockWordSupport; primary repaired and compiled it.
Luna now owns only `Components/BlockFullWords.lean`, proving fullWord of a
flattened family of block words iff pairwise disjoint carriers and full carrier
coverage. This connects the guarded actual component functional to partitions.
Build-free; no other edits authorized.
Checkpoint d4af8ce records the verified forward tight-flip increment (2029 jobs,
2578 axioms). TightFlipInverse has now compiled independently. All agents have
released files; primary adopts BlockFullWords for validation. Primary owns new
`Components/CircularGoodFlipInverse.lean` and `Components/ComponentCoefficient.lean`,
the reverse coefficient extension and finite coefficient-sum bijection.
ComponentCoefficient and BlockFullWords now compile; Astra independently
reviewed the coefficient bijection with no defect. The constancy theorem is for
fixed D and original component γ; universal-ambient/component preservation
and full subset indexing remain distinct. Astra is read-only auditing that
next architecture. Luna word_covers owns only
`Components/OrientationSubsetSum.lean`: reindex α.val.powerset via α.subselection
to all orientations whose selected set lies inside α.val. Build-free.

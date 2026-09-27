# VerticalStripLLT handoff

## Current result and verification boundary

Active goal: **formalize the full circular component proof**, with ordinary
component assembly proceeding in tandem at the user's explicit request.
The complete ordinary and aggregate circular formulas are Lean theorems.
The full ordinary and circular **component** formulas have complete audited
mathematical proofs but are **not yet complete Lean theorems**.

Latest pushed checkpoint `33cdecc` verifies whole-component undecoration,
both semantic transports, all-orientation companion sums, and residue-compatible
injective balanced lifts: **2041 jobs, 2627 axiom entries**, standard axioms only.
The next increment passes focused checks (1547 jobs): actual quotient grouping,
conditional reduction to balanced components, full integer-cover correspondence
at chosen lifts, and one compatible lift assignment for a whole component.
Independent Astra audit found no semantic defect. Full library passes **2045 jobs** and **2647 axiom entries**, standard axioms
only; source guard, width and diff checks pass. Both final component identities remain open.

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
All returned files are primary-owned. New disjoint assignments are recorded
at the end of this handoff; all subagents remain build-free. Primary remains the
sole build owner for this project, serialized across Lean projects.

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

The per-orientation finite companion and coefficient-sum constancy inside a
fixed diagram are complete. Reindex subsets by orientations, then group the
expansion by complete balanced components. The exact whole-component undecoration bridge and both component valuations
now compile.

Independent Astra architecture review found that same-area undecoration is
sufficient; full universal-area enlargement is unnecessary. Manuscript v9
`cc:lem:universal` (lines 864–880) uses only the retained long edge and normality
of its proper shorts, already provided by `normalShortEdges_of_naturalLift`.
Verified `flipComponent D.undecorated θ.toUndecorated =
(flipComponent D θ).image Orientation.toUndecorated`. This is proved by actual flip reflection and path lifting.

The balanced-lift bridge (`cc:lem:lifts`, lines 1237–1274) now has a verified
normalization of the balanced potential to original residues. Next sort those
chosen lifts and construct the ordinary interval ideal
of original natural edges compatible with those lifts. No common circular cut
may be assumed; chosen lifts can span multiple periods. The bridge transports
HRV fiber sizes, not literal integer HRV maps. Exact lifted-cover correspondence
and construction of the ordinary interval diagram remain substantial work.

Ordinary global weighted mountain-product extraction remains open. Ordered
block ownership/HRV identification, flattened compatibility, and full-word
carrier partition criteria now compile. All builds remain serialized.

Latest detailed assignment history is archived in
[the tight-flip snapshot](docs/archive/component-foundation-through-tight-flips-20260927.md).

Checkpoint `0eac2b2` records coefficient constancy (2033 jobs, 2590 axioms).
Next ownership: Astra component_review owns only
`Components/UndecoratedFlips.lean`, forward witness transport to the undecorated
diagram and original-normality of its short edges, hence strict-edge retention
along undecorated flips. Primary owns `Components/UndecoratedRecovery.lean`
and the eventual component-image assembly. Luna lanes currently edit-idle.
All subagents remain build-free; primary retains the single build slot.
Luna word_covers returned OrientationSubsetSum; primary repaired it for build.
Luna now owns only `Components/OrientationCompanion.lean`: reindex the genuine
coloring and entire-HRV finite companion over all orientations of an undecorated
diagram using coefficient vanishing off subset support. Build-free.
Astra released UndecoratedFlips; primary adopts it for compilation. Primary owns
`Components/UndecoratedComponents.lean`, reflection of flips, path lifting and
the exact image equality of whole components under toUndecorated.
Luna word_swaps owns only `Components/UndecoratedComponentSemantics.lean`,
transport of actual componentStrictEnumerator and componentHRV along the exact
component image equality, using injectivity and existing per-state semantics.
Build-free; primary is building UndecoratedComponents and owns it exclusively.
Astra component_review now owns only `Components/BalancedLifts.lean`: normalize
an actual circular balanced potential by weak-block constants to integer lifts
with the original residues, preserving all selected-edge length differences.
No common-cut or one-period assumption; build-free. Primary retains all other
source and build ownership.
Luna word_covers released OrientationCompanion; it compiles. Luna now owns only
`Components/ComponentSumPartition.lean`, grouping an arbitrary valued sum with
component-constant coefficients by the actual finite quotient of Flip reachability.
Use actual flipComponent fibers; no assumed component semantic identity.
Build-free; primary owns concrete component companion assembly.
Primary owns `Components/ComponentCompanion.lean`: sum the actual all-orientation
companion over the original component and exchange finite sums, for strict
coloring, entire lifted-HRV values, and the existing HRV monomial semantics.
No component equality or positivity is assumed.
Astra released BalancedLifts; primary is validating it. Astra now owns only
`Components/BalancedLiftReach.lean`: exact reachability and full integer-cover
correspondence at arbitrary compatible chosen lifts, with no common-cut bound.
Build-free; primary retains all other edits and builds.

Primary rejected Luna's proposed ordinary area A(rank v)=D.area(v) and equality
of rank gap with physical edge length: chosen lifts may have gaps, and q only
balances selected edges. Build the ordinary area from the number of compatible
predecessors in the ranked interval ideal. This correction is not a theorem gap
in committed source; that mistaken construction was never implemented.
Primary owns `Components/ComponentBalancedReduction.lean`: group the two
actual component companion identities and reduce their equality to the same
identity on complete balanced components, first undecorated then original D.
This is an explicitly conditional reduction, not the final component theorem.
BalancedLiftReach and ComponentSumPartition compile. Primary owns
`Components/BalancedComponentLifts.lean`, preserving one normalized potential
throughout a whole balanced component. Astra is read-only auditing quotient
grouping, the conditional balanced reduction and full chosen-lift cover proof.

Checkpoint preparation: ComponentBalancedReduction and BalancedComponentLifts
compile (1547 focused jobs). Astra independently audited actual quotient fibers,
coefficient descent, conditional balanced reduction and arbitrary integer covers;
no semantic defect found. Primary owns these returned files and integration.
Next disjoint, build-free assignments: Astra component_review owns only
`Components/IntervalDiagram.lean`, constructing an undecorated forward circular
Diagram from a finite interval-closed relation on Fin n, with exact edge relation.
Luna word_covers owns only `Components/BlockListCancellation.lean`, an iterated
signed-tail cancellation over a list of rooted blocks, preserving cross-block
compatibility explicitly. Luna word_swaps owns only
`Components/MountainProduct.lean`, finite ordered product of one-peak mountain
sums, with actual expansion over independent subset/tail choices. Primary owns
compatible-lift interval closure, sorting, integration and all Lean builds.

Primary now owns `Components/CompatibleLiftOrder.lean`, sorting injective chosen
lifts and proving interval closure of their compatible natural-edge relation.
This file is excluded from the balanced-reduction checkpoint pending its build.
Astra released IntervalDiagram; primary adopts it for compilation. CompatibleLiftOrder
compiles. Astra now owns only `Components/BalancedHRVTransport.lean`: from an
actual selected-relation conjugacy to a forward diagram, prove finite HRV and
hrvMonomial transport using chosen lifts ordered by q. No general integer
order-isomorphism is assumed, since chosen lifts can have gaps. Build-free.
Luna word_swaps released MountainProduct; primary owns compilation. Luna now
owns only `Components/SelectedColoringTransport.lean`, transporting the actual
strictOrderEnumerator along a vertex equivalence and exact selected-relation
conjugacy. Build-free; no new global semantic assumptions.
Primary owns `Components/CompatibleDiagramEdges.lean` and
`Components/CompatibleDiagramOrientations.lean`, actual ranked diagram, injection
of its edges into compatible original intervals, and orientation transport for
undecorated diagrams. Astra released BalancedHRVTransport and now read-only
plans the remaining actual-flip transport. Luna word_covers continues its owned
BlockListCancellation to supply the actual iterated flattened-word sum, beyond
the local product and pointwise indicator adapters already returned.
The user explicitly requested an independent shorter-route search. A new read-only
Astra subagent `simpler_component_route` is reviewing the proof architecture;
no source/build ownership or account change. It identified a valid simplification:
the preimage S of a balanced original component under orientationFromCompatible
need only be closed under ordinary flips. Sum the ordinary component identity
over its complete components. This drops original-to-ordinary flip reflection
and exact one-component correspondence. Keep only ordinary-to-original flips,
per-state recovery, and valuation transport. Full component identities remain open.
Astra component_review now owns only `Components/ForwardFlipNormalization.lean`:
period invariance of full lift covers and normalization of forward-diagram flip
witness tests at canonical vertex lifts. Build-free; primary retains integration.
Independent Astra shorter-route review completed and confirms the union-of-components
route. A weighted ordinary theorem is valid but generalizing the currently concrete
component-cardinality upstream APIs would cost more; derive a flip-closed subset
identity from the eventual ordinary component theorem instead. Arbitrary edge markers
cannot refine the aggregate theorem (triangle obstruction in the review).
Luna word_swaps owns only `Components/FlipClosedSums.lean`: generic equality of
sums over a flip-closed finite orientation set, assuming equality on every complete
component, using componentSetoid and quotient fibers. Build-free.
Astra released ForwardFlipNormalization for compilation. Astra now owns only
`Components/BalancedCoverTransport.lean`: exact canonical ordinary/full chosen
integer-cover equivalence under selected-relation conjugacy and ordered lifts,
including a canonical balanced potential for forward orientations. Build-free.
Primary has adopted all other returned files. Luna word_covers owns only
`Components/BlockTailFactorization.lean`, discharging the actual recursive
flattened-tail factorization premise under carrier cross compatibility.
Primary owns `Components/CompatibleDiagramSemantics.lean`, actual preimage-image
bijection of orientation states and the two component valuation sums. Astra has
released BalancedCoverTransport and now owns only
`Components/CompatibleDiagramFlips.lean`, transporting ordinary directed witnesses
into original undecorated D using normalized rank coordinates and actual chosen
lift-cover equivalence. Only this direction is required by the accepted shortcut.
All returned Luna files are primary-owned pending compilation; their agents are
edit-idle. Primary remains the only Lean build owner.
Primary owns `Components/CircularFromOrdinaryComponents.lean`, the complete
conditional circular reduction using flip-closed preimages and the proved finite
companion. Its sole semantic input is the ordinary forward-component identity.
Astra component_review now owns only `Components/HRVInitialSupport.lean`, finite
supports S_k={v | hrv(v)<k}, their one-fiber successor decomposition, and the
first incoming-closed unique-sink block identification. This supports the shorter
ordinary recursive extraction route proposed by the independent reviewer.
Independent ordinary review recommends a literal word-continuation scan mirroring
MountainProduct, then induction on actual HRV threshold supports S_k. This avoids
a global ordered-partition bijection. Per-orientation compatibility does not
descend to WordAlgebra; only the component functional does. Luna word_swaps owns
only `Components/MountainScan.lean`, the finite literal scan and its continuation
linearity. Luna word_covers remains edit-idle. All subagents build-free.

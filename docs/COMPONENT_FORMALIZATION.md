# Component formalization map: the word proof

This maps the earlier word proof of the component identities. Its ordinary
modules are in `VerticalStripLLT/Components/WordProof/` and its theorems end in
`_by_words`. The circular reduction below stays in `Components/`, because the
diagram proof uses it too. The diagram proof, which carries the plain theorem names, is mapped
in [LEAN_COORDINATION](LEAN_COORDINATION.md). The ordinary and complete circular
component identities, shifted weights, elementary positivity and degree are
proved by both. See the [completion audit](COMPONENT_COMPLETION.md) for the word
route's statements and checks.
The [earlier integration plan](archive/component-integration-through-scan-20260927.md)
is archived as implementation history; its open-task descriptions are superseded.

## Ordinary proof

- `ComponentWords`, `ComponentBijection`, `ComponentFunctional`: actual
  complete-component count, four-term identity and quotient functional.
- `WordAlgebra`, `WordConjugation`, `CauchyStep`, `FiniteWordCauchy`:
  concrete quotient and finite Cauchy factorization.
- `ColorProductPairing`, `FiniteMountainPeak`, `MountainScanPairing`,
  `ComponentScanSemantics`: actual coloring sum paired with a literal scan.
- `HRVInitialSupport`, `HRVSupportDifference`, `BlockContinuation`,
  `HRVBlockContinuation`: exact supports and signed first-block cancellation.
- `HRVScanExtraction`: actual per-state extraction by HRV threshold induction,
  with explicit `a 0 = 1` for empty fibers.
- `OrdinaryComponentExpansion`: unconditional forward-component identity.

## Circular reduction and final assembly

- `CircularFiniteCompanion`: coloring and entire periodic HRV expansions with
  identical canonical finite coefficients.
- `CircularGoodFlip`, `TightFlipInverse`, `ComponentCoefficient`: transport of
  coefficient extensions and constancy on complete components.
- `UndecoratedComponentSemantics`, `BalancedLifts`,
  `ComponentBalancedReduction`: whole-component undecoration and balanced lifts.
- `IntervalDiagram`, `CompatibleDiagramEdges`, `CompatibleDiagramOrientations`,
  `CompatibleDiagramSemantics`: actual compatible ordinary diagram and exact
  state, coloring and HRV transport.
- `ForwardFlipNormalization`, `BalancedCoverTransport`, `CompatibleDiagramFlips`:
  all six full integer-cover tests and forward flip transport.
- `FlipClosedSums`, `CircularFromOrdinaryComponents`: sum over the compatible
  preimage, a union of complete ordinary components.
- `ComponentPositive`, `WordProof/ComponentExpansion`: final circular theorem by
  words, shifted q-weights, nonnegative coefficients and elementary weighted
  degree. `DiagramProof/CircularConsequences` gives the same with the diagram
  ordinary theorem as input.

Primary retained all build ownership. Bounded Luna/Astra implementation and
independent Astra reviews supported integration. Claude supplied the extraction
candidate, verified locally without alteration. Precise provenance and model
boundaries are in the completion audit; no aggregate-to-component inference is used.

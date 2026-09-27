# Component formalization map

The ordinary and complete circular component identities, shifted weights,
elementary positivity and degree are proved. See the
[completion audit](COMPONENT_COMPLETION.md) for statements and checks.
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
- `ComponentPositive`, `ComponentExpansion`: final circular theorem, shifted
  q-weights, nonnegative coefficients and elementary weighted degree.

Primary retained all build ownership. Bounded Luna/Astra implementation and
independent Astra reviews supported integration. Claude supplied the extraction
candidate, verified locally without alteration. Precise provenance and model
boundaries are in the completion audit; no aggregate-to-component inference is used.

> Historical plan. Completed results are in [COMPLETION](../../COMPLETION.md).
> The remaining restricted-recursion issue is in [the current audit](../../RESTRICTED_BOUNCE_AUDIT.md).

# Coefficient substitution, positivity, and finite degree

These results use finite polynomial rings and the pinned Mathlib APIs.

## Checked substitution and positivity

`OrientationShift` defines `qShift` by `Polynomial.compRingHom (X+1)` and
lifts it to formal elementary expressions. It fixes each elementary generator
and HRV monomial. `qShift_orientationExpansion` maps the ordinary orientation
expression to the independently defined shifted expression.
`ShiftEvaluation.evalElementary_qShiftMap` proves coefficient substitution
commutes with finite-alphabet evaluation (declaration namespace VerticalStripLLT).

`OrientationNatural` defines the same orientation sum over
`MvPolynomial ℕ+ (Polynomial ℕ)`. Its `naturalCast` maps coefficients to ℤ.
`naturalCast_naturalOrientationExpansion` proves this maps to the existing
shifted expression. `OrientationPositive.shiftedOrientationExpansion_coeff_nonneg`
(namespace VerticalStripLLT) derives nonnegativity of EVERY q-coefficient of
EVERY formal elementary monomial coefficient by applying coefficient maps.

`coloringLLT_shifted_e_positive` combines positivity with the actual coloring
semantic bridge, uniformly in every alphabet, using one common expression.

## Checked weighted degree

`hrvFiber_card_sum` proves that HRV fiber cardinalities sum to n.
`hrvMonomial_isWeightedHomogeneous_degree` gives degree n with weight k on e_k.
The same property holds for `orientationExpansionAt` at every parameter,
and in particular the ordinary and shifted expressions.
This is weighted homogeneity, not ordinary degree in the elementary generators.

## Alphabet stability

`AlphabetStability.specializeLast_esymm` and `specializeLast_evalElementary`
(namespace VerticalStripLLT) prove specialization of the final variable to zero
commutes with elementary evaluation. `ExpansionStability` transfers this to
`coloringLLT` and iterates it: `specializeTail_coloringLLT` handles any number
of extra variables, every path, and every alphabet size.
Uniform finite-alphabet equality and this compatibility are the chosen initial
interface to the infinite-variable identity; no abstract symmetric-function
object or general symmetric-functions library is required.

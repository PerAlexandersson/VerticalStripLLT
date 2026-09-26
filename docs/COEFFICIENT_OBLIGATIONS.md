# Shift, positivity, and finite-degree obligations

These are remaining proof obligations after the ordinary semantic expansion.
They do not require a general symmetric-functions library. The primary API
audit uses the pinned Mathlib revision, not current online documentation.

## Coefficient substitution

Define the q-to-q+1 homomorphism on Q using
`Polynomial.compRingHom (Polynomial.X + 1)`, then lift it to EExpansion with
`MvPolynomial.map`. Prove that it fixes each `elementary k`, hence each
`hrvMonomial`, and maps `orientationExpansion P` to
`shiftedOrientationExpansion P`. Use the existing independent finite-sum
definitions; do not define the shifted expression by this equality.

Useful pinned APIs: `Polynomial.compRingHom` in
`Mathlib/Algebra/Polynomial/Eval/Defs.lean`, and `MvPolynomial.map_C`,
`map_X`, `coeff_map` in `Mathlib/Algebra/MvPolynomial/Eval.lean`.
Ring-homomorphism sum/product/power laws handle the orientation sum.

## Positive elementary coefficients

A narrow possible proof is a natural-coefficient lift in
`MvPolynomial ℕ+ (Polynomial ℕ)`: use the same finite orientations, ascents,
and HRV-fiber product, now with natural coefficients. Map it through
`Polynomial.mapRingHom (Nat.castRingHom ℤ)` and `MvPolynomial.map` to the
existing shifted expression. Coefficient-map identities then show each
integer coefficient is a natural-number cast. This is a proof device for the
existing expression, not a replacement semantic definition. An explicit
orientation-count coefficient formula is a stronger alternative if its
monomial-shape API is also needed for the degree proof.

The precise desired conclusion is nonnegativity of every coefficient in q
of every elementary monomial coefficient. Positivity of evaluation at one
alphabet or one positive q is insufficient.

## Degree and stability

Assign elementary generator e_k weight k. For each orientation, the HRV
fibers partition Fin n, so the sum of their cardinalities is n. This should
prove weighted homogeneity of the formal elementary expression. It must not
be confused with ordinary total degree in the elementary generators.

For finite alphabets, specialize additional variables to zero. Prove the
corresponding elementary-polynomial identity and compatibility with
`evalElementary`. Once the full bridge is available, it transfers stability
to the coloring-defined LLT polynomial. The pinned finite elementary API
already includes `aeval_esymm_eq_multiset_esymm`; inspect whether this or the
powerset definition gives the smaller proof before adding new machinery.

None of shift, positivity, weighted degree, or arbitrary-alphabet stability
is currently claimed proved in this note.

# VerticalStripLLT

Lean formalization of Per Alexandersson and Robin Sulzgruber,
*A combinatorial expansion of vertical-strip LLT polynomials in the basis of
elementary symmetric functions* (arXiv:2004.09198; published 2022).

## Main result

The ordinary expansion is proved for every valid Schröder path and every
finite alphabet, including the empty alphabet:

```lean
coloringLLT_eq_eval_orientationExpansion (P : SchroderPath n) (m : ℕ) :
  coloringLLT P m = evalElementary m (orientationExpansion P)
```

`coloringLLT` is the original finite coloring sum. `orientationExpansion` is
independently defined from normal-edge orientations and highest-reachable
vertex fibers. Their equality is a theorem, with no recurrence hypothesis.
`coloringLLT_eq_orientation_sum` exposes the formula with weights
`(q - 1)^asc` and elementary monomials indexed by the HRV fiber sizes.

`coloringLLT_shifted_eq_orientation_sum` proves the q→q+1 formula with weights
`q^asc`. `coloringLLT_shifted_e_positive` supplies one formal elementary
expression that works for every alphabet, has nonnegative coefficients in q,
and is homogeneous of weighted degree n (generator e_k has weight k).
See [Expansion.lean](VerticalStripLLT/Expansion.lean).
`specializeTail_coloringLLT` proves compatibility when any number of final
alphabet variables is set to zero.

## Model and proof structure

We use valid `north`, `diagonal`, `east` words; graph vertices and colors are
zero-based. Coloring polynomials live in
`MvPolynomial (Fin m) (Polynomial ℤ)`. Formal elementary expressions live in
`MvPolynomial ℕ+ (Polynomial ℤ)`, with a separate evaluation homomorphism.
This finite-degree model does not require a general symmetric-functions library.

The coloring and orientation models independently satisfy the column,
product, unicellular, NN bounce, and DN bounce identities. Generalized
NN/DN/ND reductions return valid paths and prove strict measure decreases.
`SatisfiesReductionRecursion.unique` uses nested strong induction on path
size, east count, and first-east height. This sufficient certificate includes
two leading-east clauses, both proved for the actual models.

Uniqueness for the original restricted manuscript-facing `SatisfiesRecursion`
is a separate, unproved claim; it is not used as an assumption in the expansion.
No recursive invariant is substituted for the coloring definition.
The source map records this distinction and the correspondence to Theorem
LLT, Theorem LLTe, and Corollary expansion.

The initial small cases are isolated under `Examples/`. The uniform column bridge,
finite path validity,
orientation bijections, HRV transport, coefficient substitution, positivity,
and weighted-degree results remain separate modules. Aristotle supplied
isolated proof candidates; Luna/Terra helped with ports and bounded proofs.
The primary owner checked all integrated results locally.

## Build and verification

Pinned toolchain: Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; the dependency manifest is tracked.
In this workspace, first confirm no other Lean/Lake build is active, then run
these commands sequentially from the project root:

```bash
lake-workspace build VerticalStripLLT.Expansion VerticalStripLLT.Circular.Expansion
lake-workspace build
lake-workspace env lean Verification.lean
```

The wrapper stores dependencies and build output under `/lake-cache/ai-projects`.
Its package-directory override emits an expected manifest warning; do not run
`lake update` in response. The axiom inventory permits only standard Lean
axioms. No proof placeholders, custom axioms, or unchecked native proofs are used.

See [the documentation index](docs/README.md),
[ordinary source map](docs/FORMALIZATION.md), and [current handoff](HANDOFF.md).
The author-supplied manuscript under `references/` is immutable.

## Circular expansion

The full circular HRV formula and e-positivity are also proved for every valid
circular Dyck/Motzkin diagram and every finite alphabet, including the empty
alphabet. The public declarations in
[Circular/Expansion.lean](VerticalStripLLT/Circular/Expansion.lean) are:

- `Circular.coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`
- `Circular.coloringLLT_shifted_eq_orientation_sum`
- `Circular.coloringLLT_shifted_e_positive`

The coloring sum and the integer-cover highest-reachable-vertex expansion are
independently defined. The equality has no recurrence, acyclicity, saturation,
or no-wrap hypothesis. One elementary expression works for all alphabets,
with nonnegative q-coefficients and weighted degree n.

The proof uses the half-square area statistic and strict rank. Strict cycles
vanish; one-bounce relations handle local reductions. For interior overlap,
reversing the columns of the merged strict component gives a valid diagram
with strictly smaller doubled area. The actual residual coloring and HRV sums
agree under this reversal; factoring and cancelling forced internal edges
closes the induction. See the [completion audit](docs/CIRCULAR_COMPLETION.md)
and [proof explanation](docs/proofs/CIRCULAR_COLUMN_REVERSAL.md).

Examples are isolated under `VerticalStripLLT/Examples/` and excluded from the
main library imports. The [ordinary flip-component expansion](docs/proofs/COMPONENT_ORDINARY_PROOF.md)
has a complete independently audited mathematical proof. The Overleaf v9
[bounded-face companion](docs/proofs/COMPONENT_CIRCULAR_FACE_PROOF.md) also
proves every circular component. Neither full component theorem is yet
Lean-verified. The new [finite companion](docs/proofs/COMPONENT_FINITE_COMPANION.md)
replaces the polyhedral argument with a coefficient recurrence and finite
cancellation, including whole-component isolation. The concrete word algebra,
conjugation, unique-sink cancellation and integer-cover rank certificates
have passed local Lean and axiom checks. See the
[component status](docs/FLIP_COMPONENT_STATUS.md). The guarded full-word count
and its linear extension now use the actual complete flip component; the
local word exchanges and all four lifted-cover certificates assemble an actual
directed flip. For ordinary forward diagrams,
`Components.componentWordCount_four` proves the contextual four-term identity,
and `Components.componentWordFunctional` descends the actual count to the word
quotient. The finite Cauchy factorization and its pairing with the actual component's
strict-coloring enumerator are now proved (`Components/ColorProductPairing.lean`).
The signed mountain-word expansion is proved; global HRV extraction and the
full component expansion remain to be assembled. The circular finite companion's
ordered-partition identity and abstract gain coefficient cancellation are proved,
as is potential independence of balanced contractions. Applying the cancellation
to these contractions and whole-component assembly remain separate obligations.
Cumulants remain outside the scope.

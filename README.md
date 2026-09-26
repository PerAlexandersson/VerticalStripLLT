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
lake-workspace build VerticalStripLLT.Expansion
lake-workspace build
lake-workspace env lean Verification.lean
```

The wrapper stores dependencies and build output under `/lake-cache/ai-projects`.
Its package-directory override emits an expected manifest warning; do not run
`lake update` in response. The axiom inventory permits only standard Lean
axioms. No proof placeholders, custom axioms, or unchecked native proofs are used.

See [the formalization map](docs/FORMALIZATION.md),
[Aristotle provenance](docs/ARISTOTLE.md), and [current handoff](HANDOFF.md).
The author-supplied manuscript under `references/` is immutable.
The [circular LLT and flip-component plan](docs/CIRCULAR_FORMALIZATION_PLAN.md)
maps the author's Overleaf outline to proposed declarations and small
milestones. It prioritizes the circular HRV expansion, then complete flip
components, reusing this finite-degree model. The circular foundation now proves the general selected-orientation coloring
identity and acyclic lifted-walk bounds. Circular HRV is defined on the
integer cover and proved to be the greatest reachable lift, independently of
its representative. Its formal elementary expansion has degree n and
nonnegative coefficients. Equality with the circular LLT coloring polynomial
and the component identities remain in progress. The full zero non-strict area family is proved for every size and alphabet,
using the actual HRV fibers and a general strict-chain coloring factorization. The manuscript's full lifted flips and complete global components are defined;
ascent invariance and the zero-normal component identity are proved.
Concrete examples live under
`VerticalStripLLT/Examples/` and are excluded from the main library imports.
Cumulants remain outside the scope.

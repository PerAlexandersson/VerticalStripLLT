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

See [the documentation index](docs/README.md),
[ordinary source map](docs/FORMALIZATION.md), and [current handoff](HANDOFF.md).
The author-supplied manuscript under `references/` is immutable.

The circular development uses natural head/length edges and highest reachable
vertices on the integer cover. The direct NN/DN identities are proved for both
actual models, along with R1, strict-cycle vanishing, the no-normal-edge base,
complete bounce search, and neutral termination. The overlapping ND branch
has proved actual polynomial identities and a complete area-induction step.
Both DD children are proved for NN/DN searches, and interior ND overlap is
proved to restart at one bounce. Mixed DD/neutral auxiliary sequences terminate
on acyclic strict graphs. Direct ND now gives both actual identities and area drops two/four; full NN
elimination is also complete. Full DN elimination preserves area and decreases strict rank. The remaining
ND assembly and final circular induction are still in progress.
Circular alphabet compatibility is proved directly from the coloring sum.
An auxiliary diagram with two distinct nonstrict corners has a checked
two-step R1 exit below the original half-square area.
Separated ND is now proved, including cyclic intermediate diagrams.
The checked outer induction has one remaining input, the interior ND step;
the unconditional circular theorem still requires its proof.
The actual coloring–HRV equality is also proved uniformly for a strict chain
plus one isolated vertex, including winding configurations and every finite
alphabet. This supplies an additional semantic base, without assuming that
all remaining interior sources belong to that family.
See [verified circular results](docs/CIRCULAR_STATUS.md) and
[remaining goals](docs/CIRCULAR_GOALS.md).

Examples are isolated under `VerticalStripLLT/Examples/` and excluded from the
main library imports. Complete flip-component expansions are downstream;
cumulants remain outside the scope.

# Ordinary vertical-strip LLT source and representation map

The ordinary expansion is complete. The architecture was recorded before
package scaffolding on 2026-09-25, following independent Astra review and the
primary source/Mathlib audit. The [completion audit](COMPLETION.md) indexes the
proved public statements. Earlier implementation plans and chronological notes
are in the [archive](archive/completed-plans/ordinary-development-map.md).

## Representation

`SchroderPath` uses valid north/diagonal/east words. Coordinates run from
(0,0) to (n,n), stay above the diagonal, and allow diagonal steps only strictly
above it. A diagonal supplies a strict graph edge; full cells supply normal
edges. Vertices and colors are zero-based.

`Q = Polynomial ℤ`, `XPoly m = MvPolynomial (Fin m) Q`, and
`EExpansion = MvPolynomial ℕ+ Q` provide the finite-degree coefficient model.
The direct coloring sum uses every map of vertices into `Fin m`, subject to
strict inequalities, with weight q to the number of normal ascents.
`evalElementary m` sends the positive-degree generator k to e_k in m variables.
A monomial in the generators records a partition by multiplicities.

The alphabet size is independent of path size. All main theorems quantify
over every m, including zero; `specializeTail_coloringLLT` proves compatibility
when extra variables are set to zero. No general symmetric-functions library
is needed.

| Alternative considered | Decision |
| --- | --- |
| Packed colorings/composition coefficients | Deferred: multiplication requires additional overlap/shuffle infrastructure. |
| Finite-variable polynomials uniformly in m | Adopted: direct semantics and existing finite sum/ring APIs. |
| Degree-indexed partition coefficients | Deferred output interface; unnecessary dependent degree changes in recursion. |
| Formal elementary generators over ℤ[q] | Adopted for the independently defined orientation expression. |

## Manuscript correspondence

Line references use the immutable author snapshot
`references/alexandersson-sulzgruber-2022/main.tex` at commit `130f7e8`.

| Source | Implemented correspondence |
| --- | --- |
| Paths, 633–645; graph, 1009–1015 | `SchroderPath`, `strictEdges`, `normalEdges` and validity lemmas |
| Colorings, 1101–1111, 1137–1144 | `admissible`, `ascentCount`, `coloringLLT` |
| Theorem recursion, 816–875 | `SatisfiesRecursion`; generic uniqueness for these restricted clauses remains open and is not used |
| Theorem LLT, 1155–1182 | Independent coloring identities; `coloringLLT_satisfiesRecursion`, `coloringLLT_satisfiesReductionRecursion` |
| Orientations/HRV, 1267–1326 | `Orientation`, `orientationAsc`, `reachable`, `hrv`, `hrvFiber`, `hrvMonomial` |
| Formula, 1349–1355 | `orientationExpansion`, with unshifted weights `(q−1)^asc` |
| Theorem LLTe, 1361–1364 | Independent orientation identities and `orientationExpansion_satisfiesReductionRecursion` |
| Corollary expansion, 1369–1373 | `coloringLLT_eq_eval_orientationExpansion`, `coloringLLT_eq_orientation_sum` |
| Shifted e-positivity | `coloringLLT_shifted_eq_orientation_sum`, `coloringLLT_shifted_e_positive` |

## Actual proof route and retained caveat

`SatisfiesReductionRecursion` adds sufficient reduction clauses to the original
restricted certificate. Both concrete models satisfy it independently, and
`SatisfiesReductionRecursion.unique` uses size, east-step count, and the absolute
height before the first east step. Generalized bounce identities have their
own contact-count induction. All required path-validity and measure-decrease
conditions are proved.

This yields equality of the direct coloring sum and independent HRV expression.
No recursive invariant is renamed LLT. The originally considered recursive
construction was superseded by uniqueness of the two concrete models.

[RESTRICTED_BOUNCE_AUDIT.md](RESTRICTED_BOUNCE_AUDIT.md) retains the genuine
open issue about uniqueness from the manuscript's narrower clauses. It is not
a hypothesis of the completed main theorem and is not a proved counterexample.

The source works over ℚ(q); our proof cancels nonzero polynomial factors over
integral polynomial domains. Line 2010's `F_ne=1` conflicts with the initial
condition and coloring calculation `F_ne=e₁`; the latter is used. The empty
path has value 1. Reference files were not changed.

The repository pins Lean 4.34 and its Mathlib revision in the toolchain and
manifest. [README](../README.md) gives the serialized external-cache build
workflow; [ARISTOTLE.md](ARISTOTLE.md) preserves external proof provenance.

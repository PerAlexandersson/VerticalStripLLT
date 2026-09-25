# Ordinary vertical-strip LLT formalization map

Decision recorded 2026-09-25, before package scaffolding. The primary Astra
audited the author-supplied source and cached Mathlib independently of the
read-only Astra reviewer `/root/architecture_review`. The reviewer made no
edits and ran no builds. We adopt the common recommendation below.

## Representation decision

We use valid words in `n`, `d`, `e` as canonical paths. Their coordinates start
at `(0,0)`, end at `(n,n)`, never cross below the diagonal, and permit a
diagonal step only strictly above it. Words make the manuscript's local
substitutions literal. A decorated area-sequence interface can be added later
if a proof needs it; we do not maintain two canonical representations now.

We put `Q := Polynomial ℤ` and `XPoly m := MvPolynomial (Fin m) Q`.
For each path, `coloringLLT P m` is the finite sum over maps from its vertices
to `Fin m`, discarding colorings that violate strict edges. A summand is
`C (X ^ ascentCount) * ∏ v, X (color v)`. Only non-strict edges count as ascents.
Vertex and color labels are zero-based; paper label `i` corresponds to `i-1`.

The ambient variable count `m` is independent of path size. All eventual
theorems quantify over `m`, including zero. Fixing `m = size P` would obstruct
concatenation in a common ring. One specialization does not prove the
infinite-variable identity. Equality for every finite alphabet is our initial
statement of that identity; a formal stability/coefficient interface is a
separate milestone.

For formal elementary expressions we use
`EExpansion := MvPolynomial ℕ+ Q`: a finite sum of monomials in positive-degree
elementary generators. This is already a finitely supported coefficient
representation, with multiplication supplied by Mathlib. Generator `k`
has weight `k`; degree preservation will be proved with a weighted-degree
predicate. Monomials encode partitions by multiplicities without sorting.
The homomorphism `evalElementary m` sends generator `k` to Mathlib's
`MvPolynomial.esymm (Fin m) Q k` and acts identically on `Q`.

| Alternative | Audit and decision |
| --- | --- |
| Packed-coloring/composition coefficients | Faithful finite data, but overlap/quasishuffle multiplication would add infrastructure before the first recursion proof. Defer. |
| Fixed-variable polynomials, uniformly in `m` | Direct coloring semantics and existing ring/sum APIs. Adopt. |
| Degree-indexed `n.Partition →₀ Q` | Mathlib partitions and `esymmPart` exist, but every recursive product changes the degree index. Defer as an output interface. |
| Formal positive elementary generators | Existing sparse polynomial ring supplies sums/products; interpretation remains separate. Adopt. |

This is a small algebra of expressions, not a general symmetric-functions
library. We do not need the fundamental theorem of symmetric polynomials to
construct or evaluate it. Nor do we assume evaluation is injective for a fixed
small alphabet.

## Source map and proposed declarations

All line references below refer to the immutable author snapshot
`references/alexandersson-sulzgruber-2022/main.tex` at commit `130f7e8`.
Names in this table are planned interfaces, not claims of completed proofs.

| Source | Lean interface and obligation |
| --- | --- |
| Paths, 633–645 | `Step`, `SchroderPath`, endpoint/validity checks; later `concat`, `columnPath`. |
| Decorated graph, 1009–1015 | `strictEdges`, `normalEdges`; diagonal endpoints are strict, full cells below the path are normal. Prove orderedness and disjointness. |
| Colorings, 1101–1111; `lltDefinition`, 1137–1144 | `admissible`, `ascentCount`, `coloringLLT`, defined directly by finite coloring sums. |
| Theorem `recursion`, 816–875 | `SatisfiesRecursion`, `recursion_unique`, eventually `existsUnique_recursion`. Include empty-path normalization explicitly. |
| Theorem `LLT`, 1155–1182 | `coloringLLT_columnPath`, `coloringLLT_concat`, `coloringLLT_unicellular`, two single-bounce relations, `coloringLLT_satisfiesRecursion`. The full source theorem also contains the third bounce type and arbitrary bounce length. |
| Orientations, 1267–1276 | `Orientation`, `orientationAscentCount`: choose directions for normal edges, force strict edges upward. |
| HRV, 1315–1326 | `upwardReachable`, `highestReachable`, `hrvBlockSizes`: use reflexive reachability through strict and ascending edges only. |
| `conjFormula`, 1349–1355 | `orientationExpansion`: sum `(X-1)^asc` times formal elementary monomials. A separately named shifted expansion uses `X^asc`. |
| Theorem `LLTe`, 1361–1364 | `orientationExpansion_satisfiesRecursion`, proved by the orientation bijections. |
| Corollary `expansion`, 1369–1373 | `coloringLLT_eq_eval_orientationExpansion P m`, followed by the shifted identity and nonnegative formal coefficients. |

The defining display is `LLTe(q+1) = Σ q^asc e_λ`. Thus unshifted orientation
weights are `(q-1)^asc`; confusing these conventions changes the theorem.

## Recursion, termination, and semantic bridge

The uniqueness proof at 1996–2044 uses the lexicographic measure
`(size, number of east steps, absolute height before the first east step)`.
The third entry is the vertical coordinate `z`, not area or distance from the
diagonal. We will expose decrease lemmas before defining the algorithm.

1. A nonempty path with one east step is `n d^(n-1) e`: return `e_n`.
2. If the first east step starts at distance one above the diagonal, split
   into two smaller nonempty paths and multiply their values.
3. If the preceding step is north, the unicellular relation produces one
   path with fewer east steps and one with smaller first-east height.
4. If it is diagonal, generalized bounce relations reduce first-east height.

The separate bounce reduction theorem, 1853–1990, inducts on the number of
bounce points. Its proof precedes recurrence uniqueness and the deterministic
algorithm's final case.

Defining `recursiveInvariant` and proving termination does not establish all
recurrence identities. We will prove coloring identities independently and
use the selected reductions to prove the named bridge
`eval_recursiveInvariant_eq_coloringLLT`. The later named bridge
`recursiveInvariant_eq_orientationExpansion` requires the orientation
identities and uniqueness. Neither bridge may be supplied as an assumption
in a theorem advertised as the ordinary LLT expansion.

## Integral coefficients and source discrepancies

The manuscript works over `K = ℚ(q)` (macro 188, context 622). It divides or
cancels `q-1` in relation equivalence and bounce reduction (1530–1535, 1645,
1904 onward, 1979). Over our integral polynomial rings we must prove
injectivity of multiplication by `X-1`, and use cancellation rather than
division. These implications are not valid in an arbitrary `ℤ[q]`-algebra
without an appropriate torsion-freeness hypothesis.

Line 2010 says `F_ne = 1`; the initial condition at 823–828 and its coloring
proof at 2306–2321 give `F_ne = e₁`. We use the latter. The empty path gets
value `1` explicitly. No reference files are altered.

## API audit and reproducibility

We select the cached Lean `v4.34.0` and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`. The project manifest will pin the
exact dependency closure; `lake-workspace` recognizes the revision-specific
shared checkouts. No cache sources are edited and no dependency update is
needed to initialize from this verified closure.

- `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean`: `esymm`,
  `esymm_one`, `esymm_eq_sum_subtype`, `esymmPart`, `esymmPart_indiscrete`.
  Lean MCP local search independently confirmed `esymm_one`.
- `MvPolynomial.eval₂Hom` interprets elementary expressions. Ordinary
  polynomial coefficients keep the `q` variable distinct from the alphabet.
- `Mathlib/Combinatorics/Enumerative/Partition/Basic.lean` supplies partitions
  as positive multisets with a prescribed sum for a later output interface.
- `Finsupp.linearCombination` is available if that output interface is needed.
- `Finset` sums, finite function types, and `Fin.prod_univ_two` provide the
  first coloring checks without custom enumeration infrastructure.

Rust capability check: read `rust/docs/LIBRARY_GUIDE.md`, ran workspace Cargo
metadata, and searched `sym-poly/sym/src/llt.rs`, tests, and examples. Existing
`unicellular_llt` and constrained-coloring APIs can support future numerical
checks. This slice writes Lean definitions and proofs, no new external
enumeration program or polynomial sequence. No Rust changes are needed.

## Milestones

1. **Planning:** this reviewed decision and source map, committed before code.
2. **First slice:** generic finite coloring semantics; valid `ne`, `nde`,
   `nnee`, `nene`; the `e₁` base case and size-two unicellular identity;
   evaluate formal `e₂` on `nde`. Two-color results must be labeled as such.
3. **Basic families:** concatenation, arbitrary strict-chain base identities,
   graph decoding invariants, finite-alphabet specialization.
4. **Local relations:** general unicellular and single-bounce coloring proofs.
5. **Uniqueness:** bounce reduction, decrease lemmas, recurrence uniqueness.
6. **Recursive expressions:** deterministic construction, degree preservation,
   named equality with coloring semantics.
7. **Orientations:** HRV, elementary expression, recurrence identities.
8. **Ordinary theorem:** equality of the independently defined objects,
   shifted positivity and stable coefficient interface.

Circular LLTs, cumulants, and flip components remain downstream.

## First slice delivered

Milestones 1 and 2 are complete. Related Lean:
`VerticalStripLLT/SmallCases.lean`, especially `coloringLLT_singleton`,
`coloringLLT_pair_unicellular`, and
`coloringLLT_normalPair_eq_evalElementary_two`. The first two are uniform in
the alphabet size; the last interprets `e₁²+(q−1)e₂` in two variables.
`coloringLLT_empty` fixes the size-zero normalization. The original Astra
reviewer also independently checked the implemented path decoder and found
its zero-based normal/strict edge conventions faithful to the source.

## General base case and concatenation foundations delivered

Related Lean: `ColumnBase.lean`, `coloringLLT_column` and
`coloringLLT_column_eq_evalElementary` establish the full initial condition
`G_(n d^k e)=e_(k+1)` for every finite alphabet, including an empty alphabet.
`ElementaryColorings.lean`, `increasingColoringSum_eq_esymm`, gives the finite
subset bijection used in this proof; its candidate originated from Aristotle.

`PathInvariants.lean` proves orderedness and disjointness of graph edges.
`PathBounds.lean` provides endpoint bounds. `Concat.lean` defines valid path
concatenation and proves append/translation laws for validity and both edge
scanners. These establish the graph foundations of milestone 3. The coloring
multiplicativity identity and finite-alphabet specialization are still open;
we do not mark all of milestone 3 complete.

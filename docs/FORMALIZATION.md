# Ordinary vertical-strip LLT formalization map

Decision recorded 2026-09-25, before package scaffolding. The primary Astra
audited the author-supplied source and cached Mathlib independently of the
read-only Astra reviewer `/root/architecture_review`. The reviewer made no
edits and ran no builds. We adopt the common recommendation below.

## Current theorem status

The ordinary finite-alphabet expansion and shifted e-positivity are now proved
in `Expansion.lean`, with no recurrence or expansion assumption on the public
main theorem. `coloringLLT_eq_eval_orientationExpansion` is uniform in n, P,
and m; `coloringLLT_shifted_eq_orientation_sum` exposes the source formula.
`coloringLLT_shifted_e_positive` gives nonnegative q-coefficients and weighted
degree n for one expression valid in every alphabet.

Both concrete recurrence certificates are proved independently. Uniqueness
uses `SatisfiesReductionRecursion`, the explicitly stronger sufficient
certificate recorded below. Original restricted-recursion uniqueness remains
unproved and is not used. The earlier recursive-invariant implementation plan
was replaced by direct uniqueness; no recursively defined object is renamed LLT.
Alphabet-specialization compatibility is proved by `specializeTail_coloringLLT`.
The sections below preserve the representation decision and source audit;
chronological open-obligation notes are superseded by this status.

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
| Orientations, 1267–1276 | `Orientation`, `orientationAsc`: choose directions for normal edges, force strict edges upward. |
| HRV, 1315–1326 | `reachable`, `hrv`, `hrvFiber`, `hrvMonomial`: use reflexive reachability through strict and ascending edges only. |
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
scanners. `ColoringConcat.lean`, `coloringLLT_concat`, now proves the coloring
multiplicativity identity, using disjoint embedded edge sets and factoring
admissibility, ascent counts, vertex monomials, and finite sums. This is
Proposition `coloringProperties` (ii), manuscript lines 2323–2339. The proof
candidate originated from Aristotle and was ported and checked locally.
Finite-alphabet specialization remains open; milestone 3 is not fully complete.

## Supporting finite-sum and local-path identities

`ColoringSplit.lean` supplies `coloringSplitEquiv`, `sum_colorings_split`, and
`sum_colorings_split_mul` for all sizes and alphabet cardinalities, including
zero. These isolate the finite-sum step of coloring multiplicativity from its
graph and weight factorization.

`UnicellularPath.lean` proves that a valid `U d V` has valid resolutions
`U ne V` and `U en V`. It also proves that `U en V` has the same normal-edge
scanner as `U d V`, and the two resolutions have the same strict-edge scanner.
These supply the path resolutions for Proposition `coloringProperties` (iii),
manuscript lines 2341–2352.

`MarkedDiagonal.lean` locates the endpoint `(x,y)` of `U`, constructs the
marked vertex pair, and proves strict-edge membership. `UnicellularWeight.lean`
proves the pointwise weight identity under the four explicit edge-set
equalities, by splitting admissibility and the marked color inequality.

`Unicellular.lean` proves the changed edge sets are obtained by insertion of
the marked pair. Strict/normal disjointness proves freshness. The pointwise
weight identity then yields `coloringLLT_unicellular` by summation, uniformly
in all finite alphabets. Aristotle supplied the candidate; Luna ported it and
primary verified it locally. No recursive invariant is used in this proof.

The first three recursion clauses are now proved. For the remaining bounce
clause, `ColoringSwap.lean` supplies the swap involution, increasing/decreasing
coloring equivalence, and monomial preservation. Its admissibility and ascent
effects still require graph hypotheses. See `BOUNCE_PLAN.md` for the audited
single-bounce scope and remaining proof decomposition.

## First single-bounce identity delivered

`FirstBounce.lean`, `coloringLLT_firstBounce`, proves the `nn` clause of
Theorem `recursion` (851–871) directly for the coloring-defined polynomial,
for every finite alphabet. Its word hypotheses are validity, the prefix-height
return equation, the endpoint gap, and the manuscript's no-east middle word.
The source coloring argument is at 2417–2519.

`BounceScanners.lean` proves raw endpoint bounds and scanner swap facts.
`FirstBounceGraph.lean` constructs the common background `R e e n W` and
proves all four changed-edge identities, freshness, and swap invariance.
`BounceWeight.lean` is independent of that geometry: its graph-conditional
weight theorem uses the piecewise coloring involution. The final theorem
combines these layers; it assumes no graph identities or recurrence.

The scanner argument actually permits east steps in V under the remaining
endpoint hypotheses. The public theorem retains the no-east hypothesis for
matching the manuscript's bounce decomposition. Terra independently checked
this strengthening and the displacement-preserving background.

`WordCounts.lean` proves endpoint coordinates from the three step counts and
north/east count equality for valid paths. `PolynomialCancellation.lean`
proves nonzero q−1 and cancellation in `MvPolynomial σ (Polynomial ℤ)`.
These are prerequisites for the separate recursion/termination work in
`RECURSION_PLAN.md`; no recursive invariant or uniqueness theorem is claimed.

## Coloring recurrence delivered

`SecondBounce.lean`, `coloringLLT_secondBounce`, proves the `dn` recurrence
clause and the source's single-bounce Theorem `colorings:bounceII` (2523–2535)
uniformly in finite alphabets. `SecondBounceScanners.lean` compares the local
prefixes; `SecondBounceGraph.lean` reuses the first-bounce background and
proves the inserted edges and symmetries; `SecondBounceWeight.lean` proves
the interval-based coloring involution, including equality boundary cases.

`Recursion.lean` defines `SatisfiesRecursion` with named fields for empty
normalization and the five recurrence clauses. It is generic in a commutative
ring, q, elementary values, and a path invariant. The bounce fields retain
no-east middle words. `ColoringRecursion.lean`,
`coloringLLT_satisfiesRecursion`, supplies every field for the independently
defined coloring sum. This is a semantic recurrence theorem, not a recursive
definition or a uniqueness/expansion theorem.

The arbitrary-length bounce identities remain open. The restricted
recurrence audit in `RESTRICTED_BOUNCE_AUDIT.md` records a source-proof step
that needs justification in the generic layer; it does not invalidate any
checked coloring identity or establish a counterexample to the manuscript.

## Third single-bounce coloring identity delivered

`ThirdBouncePath.lean` proves the valid reverse local swap `nd → dn` under
the strict prefix gap, proves the common endpoint equations, and derives that
gap from the return certificate. `ThirdBounceWeight.lean` proves invariance
under equal step words and `coloringLLT_firstBounce_general` for arbitrary
middle V directly from the graph lemmas.

`ThirdBounce.lean`, `coloringLLT_thirdBounce`, constructs both valid successors
Q=`U nd V ed W`, R=`U dn V ed W` and proves, for every finite alphabet,
`G_(U nd V de W) = C(q−1)G_Q + C(q)G_R`. Its algebra combines four unicellular,
two first-bounce, and one second-bounce identity, then cancels the already
proved nonzero factor q−1. The first-bounce instance with middle eV uses the
new unrestricted coloring theorem. It is never inferred from the restricted
`SatisfiesRecursion` predicate. Thus the generic audit obligation remains
separate from this completed concrete coloring proof.

The conditional first-east product and north-predecessor branches are now
`firstEast_product_reduction` and `firstEast_north_reduction`. Both work for
an arbitrary commutative-ring recurrence witness and include exact strict
measure decreases. They do not yet constitute an exhaustive reduction or a
uniqueness proof. See `RECURSION_PLAN.md` for the remaining diagonal branch.

The orientation model is now defined independently in `Orientation`, `HRV`,
and `OrientationExpansion`: `orientationExpansionAt` isolates the ascent
parameter, with unshifted and shifted wrappers. Reachability maximality,
HRV idempotence, fiber nonemptiness, and empty-path normalization are proved.
The detailed representation decision is `ORIENTATION_MODEL.md`; the column, product, and unicellular orientation identities are now proved.
The arbitrary-path equality with coloring semantics remains open.

`BounceSeed.split` and `BounceSeed.dd_child` preserve the exact return index
and the strict child gap. `BounceSeed.trace` constructs a finite prefix trace
by strong induction on word length. This is a word-geometry certificate;
transformed-path validity and generalized-bounce value identities are separate.

`orientationExpansionAt_column k z` now proves the independent orientation
initial condition uniformly in the ascent parameter z. Its specializations
are `orientationExpansion_column` and `shiftedOrientationExpansion_column`.
`coloringLLT_column_eq_eval_orientationExpansion k m` is the resulting
end-to-end equality for all columns and all finite alphabets, including zero.
The arbitrary-path corollary remains open.

The sufficient recurrence certificate for the main expansion is now separated
from the exact manuscript-facing restricted predicate; see
`REDUCTION_CERTIFICATE.md`. Its two extra leading-east identities must be proved
independently for both concrete models; the coloring witness is checked. The final expansion remains
unconditional, and exact restricted-recursion uniqueness remains open.

`orientationExpansionAt_concat` now proves independent orientation
multiplicativity for arbitrary valid paths, uniformly in the ascent parameter.
Its modules separate edge/orientation splitting, reachability/HRV transport,
and the finite sum. `HRVCongruence`, `OrientationInsert`, and
`OrientationInsertStep` provide checked fresh-edge primitives for unicellular.
The sufficient certificate and its coloring witness, generic third-bounce
consequence, and ring-map transport are implemented; they are distinct from
an unproved uniqueness assertion for the original restricted predicate.

`orientationExpansionAt_unicellular` completes the independent orientation
initial/product/unicellular milestone, corresponding to Proposition
`O:e-mult-diag`, especially manuscript lines 2762–2820 for the edge bijection.
`OrientationTransport` reindexes equal normal-edge sets;
`OrientationInsertSum` splits the fresh edge into false/true summands and
proves the corresponding HRV monomials. No coloring identity is used.
`OrientationSpecializations` records the ordinary and shifted consequences.

`SecondBounceGeneral` now exports unrestricted-middle DN coloring semantics;
the original restricted theorem is a corollary with unchanged statement.
The sufficient certificate explicitly includes NN and DN leading-east
clauses, with coloring witnesses and map transport for both.
`BounceCoordinates`, `BounceDecomposition`, and its properties separately
certify the single-bounce coordinates, terminal-pair extraction, east-free
parts, and closure under raising the final diagonal by a north step.
These word facts do not assert generalized transformed-path validity or values.

The NN case of manuscript `bounce_reduction` (1853–1993) is now proved for
the explicitly stronger sufficient certificate as
`SatisfiesReductionRecursion.generalizedFirstBounce`. It includes a valid
successor and strict measure decrease; its value theorem has arbitrary
continuation and path size. `SatisfiesReductionRecursion.dd_step` in `GeneralizedBounceDD.lean` proves
the common linear DD diagram
with explicit successor validity and two induction equations. The word
adapter `SchroderPath.evalWord` never asserts a recurrence for invalid words.
Generalized DN/ND and the manuscript's exact restricted uniqueness remain open.

## Independent NN orientation bounce delivered

Manuscript `orientations:bounceI` (2924–2944) is
`orientationExpansionAt_firstBounce_general`. It allows unrestricted middle V
and parameter z, with coefficient C(z+1). The ordinary and shifted corollaries
are in `OrientationFirstBounceSpecializations`.

The proof uses the actual orientation sum. `BounceHRVCore` connects arbitrary
relation maxima to `hrv` and the fiber monomial. `BounceOrientationOps`,
`BounceRelations`, `BounceDistinguished`, and `BounceTransport` separate the
edge choices and HRV transport. `BounceMatching` proves the matching bijection
and its ascent/monomial properties; `BounceAssembly` sums it.
No recursive invariant or coloring/orientation equality is assumed. The
independent DN orientation identity and full semantic bridge remain open.

The DN and ND cases of `bounce_reduction` are now proved as
`SatisfiesReductionRecursion.generalizedSecondBounce_word` and
`generalizedThirdBounce_word`. Separate `GeneralizedSecondBounceReduction`
and `GeneralizedThirdBounceReduction` modules package the identities with
valid paths, preserved east count, and strict first-east-height decrease.
The independently checked `firstEast_prefix_cases` supplies the remaining
geometric case split. Recurrence uniqueness is the next integration target.

`OrientationShift` proves coefficient substitution q→q+1 maps the ordinary
orientation expression to the independently defined shifted expression.
Positivity and weighted homogeneity remain distinct unproved obligations.

## Sufficient-certificate uniqueness delivered

`SatisfiesReductionRecursion.unique` proves equality of any two invariants
with the same sufficient reduction certificate over a domain where q−1 is
nonzero. Its proof uses nested strong induction on size, east count, and
first-east height. `BounceAgreement` handles the three terminal bounce cases
by identifying successor words and applying lower-height agreement.
`ColoringCharacterization.coloringLLT_eq_of_satisfiesReductionRecursion`
(the declaration is in namespace `VerticalStripLLT`) specializes uniqueness
to the coloring polynomial. Its recurrence hypothesis remains explicit.

This is not uniqueness for the unchanged restricted manuscript predicate,
and does not establish the orientation expansion until its independent DN
identity and full certificate are proved. No recursive object is used as a
replacement for either semantic definition.

## Main expansion delivered

The unrestricted DN orientation identity is
`orientationExpansionAt_secondBounce_general`, using seven separate helper
modules and a final graph instantiation. `orientationExpansion_satisfiesReductionRecursion`
bundles the independently proved orientation clauses. Its ring-map transport
through `evalElementary` and `coloringLLT_eq_of_satisfiesReductionRecursion`
prove `coloringLLT_eq_eval_orientationExpansion`.

Theorem LLT's coloring recurrence is `coloringLLT_satisfiesRecursion`; the
stronger coloring witness is also proved. Theorem LLTe's clauses are the
`toSatisfiesRecursion` projection of the proved orientation certificate.
Corollary expansion is the unconditioned bridge and its shifted e-positive
corollary. The proof establishes the concrete ordinary expansion without
asserting the unproved original restricted uniqueness statement.

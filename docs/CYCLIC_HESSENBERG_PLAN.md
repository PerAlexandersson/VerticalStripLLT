# Cyclic Hessenberg LLT implementation

Status: complete and kernel checked, 2026-11-12. Final Lean source:
`09b32d62b4a5fb9a0ef0e63fb2ef2505720cfd8d`; serialized Laplace receipt
`20261112T122307-ff9f3c03`, exit 0, 2496 jobs. The full library, cyclic audit
and existing-result audit pass. A build-time guard checks all 110 cyclic
declarations against exactly `propext`, `Classical.choice`, `Quot.sound`.
All five public endpoints and every regression below are checked. Toolchain,
manifest and existing ordinary/circular/component proofs are unchanged.

## Scope and source correspondence

We implement an additional application under
`VerticalStripLLT/CyclicHessenberg/`, in namespace
`VerticalStripLLT.CyclicHessenberg`. Its source polynomial is the finite sum
over canonical loop covers and colors, defined before transfer kernels or
elementary expansions. For every positive layer count, we prove one formal
elementary expression whose evaluation in every finite alphabet equals this
polynomial after `q ↦ q+1`. Its coefficients lie in `ℕ[q]`.

The mathematical specification is `FINDINGS.md`, Sections 13–15, and
`cyclic-llt-e-expansion.tex` in the Cyclic-LLT-e-positivity project. The
2026-11-11 plan in AlexanderssonFormalizations supplies the detailed theorem
contracts. This document is their standalone implementation map; that
monorepo and the research manuscript remain read-only.

| Manuscript locator | Formal milestone |
| --- | --- |
| `eq:ties`, `eq:loopColors`, `lem:loopColors` | Independent colored covers and sorted-loop bijection |
| `eq:layerAscents`, `eq:layerMatrix`, `eq:openMatrix` | Layer kernels and ordered matrix product |
| `lem:layerExchange`, `eq:exchangeFirst`, `eq:exchangeSecond` | Scalar exchange and product closure |
| `lem:diagonalFourTerm` | Contextual balance of diagonal weights |
| `lem:positiveDeletion`, `eq:minimumSlide` | Ring-valued deletion with unequal suffixes |
| `lem:colorRecurrence`, `eq:threeCancellations` | Contextual finite signed-list insertion |
| `eq:positiveRecurrence` | Closed natural-coefficient recursion |
| `thm:cyclicExpansion` | Explicit canonical-cycle expansion |
| `cor:matchingExpansion` | Matching expansion and marked-ascent counts |

The source identification with Kim–Oh's Definition 6.1 uses their Theorem 6.3
and its composition-indexed proof. We formalize this finite-alphabet combinatorial
model and its weighted bijection in the `CyclicHessenberg` namespace.

## Independent architecture review and decision

The read-only Astra agent `cyclic_architecture_review` reviewed the complete
specification and standalone interfaces before the generic implementation.
It approved the elementary kernel route, with the following decisions adopted
by the primary integration owner:

* Orders are lists with no repetitions and a specified finite named support.
  Deleting vertices preserves their original names and order.
* Kernels are finite matrices on those orders. We extend an entry by zero to
  invalid lists, so scalar identities can retain explicit exterior lists.
  Compatibility is the two scalar laws; matrix commutation will be derived.
* Both prefix and suffix restrictions allow different fixed row and column
  orders. Prefix lengths agree because their supports agree. The first source
  checkpoint includes these restrictions and the signed intermediate kernel.
* Canonical covers use `Fin (n+1) → Equiv.Perm (Fin k)`, with identity first
  and last boundaries. Their feasibility and ascent events are independent
  of transfer matrices. Main source-facing endpoints require `0 < n`.
* Root deletion is proved over a ring before positivity. The minimum-slide
  proof needs an insertion/erasure equivalence, including the empty list.
* Color insertion uses finite signed lists and arbitrary exterior contexts.
  Contextual equality must be stable under adjoining another finite sum.
  Commuting the inverse color-class sum with the letter sum is a separate
  derivation from the inverse identities; it is not multiplicativity of the
  functional. The existing quotient-word proof is not an implementation input.
* The recursive expansion needs additivity and scalar linearity in its kernel
  before cycle unrolling. Its empty value is the constant kernel entry, which
  need not be `1` for a generic kernel.
* Canonical cycle displays include singleton cycles. Matching propagation is
  explicitly successive composition, with
  `ω (cycleSource ω[i]) = cycleTarget ω[i]`.

No review agent ran a build or edited source. A bounded Luna delegate drafted
only `Data.lean`; the primary reviewed and adopted it, and owns integration.

The Astra reviewer independently checked the later finite-word decomposition.
We use finite `MonoidAlgebra` sums and `ContextEq`, with no quotient and no
assumption that the evaluating functional is multiplicative. Multiplication
congruence is proved by finite expansion. Both inverse identities and the
full repeated-letter sandwich are checked before conjugating commutators.
`wordAd_terminates` uses an explicit full-support degree bound in every
context; `finite_weight_shift` retains the boundary summand explicitly.
The subsequent independent review approved homogeneous `lengthSlice` extraction:
for each pair of exterior words and degree, instantiate the conjugation and inverse
identities for that length slice and use its explicit finite bound. The checked
`wordAd_eq_signedSublistMountain` implements this route without a polynomial lift.
The prefix/color-product bridge is proved in `ColorPrefixEvaluation.lean` and
`ColorRecurrence.lean`.

The next review selected the pure finite-subword/coloring bijection. We adapt the
combinatorial proofs from the existing word proof locally, without importing its
quotient dependencies. For residual supports we first remove forbidden-letter
factors using contextual annihilation, then apply the full-support subword
bijection. Actual prefix-support cancellation supplies the required annihilation.
The single imported `Components.WordProof.DisjointSubsetSums` helper is purely a
finite-sum bijection; it imports only Mathlib and no component or quotient theorem.

The independent cycle review selected lists of root/tail pairs. The concatenated
root-first blocks form an order of the support; each tail vertex is smaller than
its root and roots strictly decrease. Rotate each block left for the target order.
The display permutation is source-position inverse followed by target-position,
which makes the direction theorem immediate. The inverse uses orbit maxima and
`if p r = r then [r] else p.toList r`: pinned Mathlib's `toList` omits fixed points.
Prove literal orbit reconstruction and both inverse laws before transferring a
finite instance. A separate max-deletion equivalence supplies the display-sum
recurrence, which is valid for arbitrary kernels before any exchange hypothesis.

## Standalone dependencies

Baseline is `f93e8755b473528d95b3e5d8f7c08d07af9e4fa0` in the public
`PerAlexandersson/VerticalStripLLT` repository. Lean is `v4.34.0`; Mathlib is
`5ed2965256430c3649e86755f9576b54eca72435`. Keep both pins and the manifest.

We reuse `Q`, `XPoly`, `EExpansion`, `elementary`, `evalElementary` from
`Polynomial`; `NEExpansion`, `natElementary`, `naturalCast` from
`OrientationNatural`; `qShift` and `xQShift` from `OrientationShift` and
`ShiftEvaluation`; and `increasingColoringSum_eq_esymm` from
`ElementaryColorings`. Here `Q` means `Polynomial ℤ`. The shifted layer
weight is `(1 + Polynomial.X)^a` and is shifted exactly once.

The private `naturalCast_elementary` lemma cannot be referenced externally;
its elementary simplification can be proved from the public definitions.
Imports of existing coefficient interfaces may transitively load orientation
definitions, but new correctness proofs do not use component positivity.

This repository has no monorepo `Shared` library, challenge catalog, Comparator
runner, or import-checking scripts. We do not invent those dependencies.
Sources follow the existing ordinary `import` convention and `autoImplicit =
false`. Final audit entry points follow `Verification.lean` and
`DiagramProofVerification.lean`.

## Implementation gates

| Gate | Modules under `CyclicHessenberg/` | Required result |
| --- | --- | --- |
| 1 | `BoundaryOrder`, `Data`, `Kernel` | Finite orders, scalar/matrix equivalence, product closure, unequal prefix/suffix closure |
| 2 | `RootDeletion` | Full signed-to-positive identity as kernels, insertion equivalence, residual compatibility and coefficient maps |
| 3 | `Coloring`, `ColorClassSums`, `ColorInsertion`, `Expansion` | All-alphabet evaluation, natural coefficients, weighted homogeneity, expansion linearity |
| 4 | `Loops`, `Layer`, `LayerExchange`, `LoopKernel` | Independent source model and semantic bridge, spectator-aware exchange proof |
| 5 | `CycleDisplay`, `CycleEquiv`, `CycleExpansion`, `MatchingExpansion`, `MatchingCoefficients` | Explicit cycle/matching formulas, coefficient factor and finite marked-ascent count |
| 6 | Public root, cyclic examples/challenges, audit | Kernel checks, axiom audits and existing-paper regression |

The public theorem file is `VerticalStripLLT/CyclicHessenberg.lean`; it contains
the five main declarations and their proofs. Examples are in
`VerticalStripLLT/Examples/CyclicHessenberg.lean`. The historical import path
`VerticalStripLLT/Challenges/CyclicHessenberg.lean` imports the public theorem file.
The declaration names remain in `VerticalStripLLT.Challenges.CyclicHessenberg`.
The audit is `CyclicHessenbergVerification.lean`, importing the additional
`CyclicHessenberg/Audit.lean` module. The latter makes the axiom queries
available through the constrained remote target interface.
The insertion/erasure equivalence is isolated in the additional helper
`CyclicHessenberg/OrderInsertion.lean`, between BoundaryOrder and RootDeletion,
so its list bookkeeping can be implemented and reviewed independently.
The additional `CyclicHessenberg/MatrixExchange.lean` isolates the generic
finite-involution matrix calculation used to derive product closure; it does
not assume commutation in place of the two scalar laws.

All six implementation gates have passed. The modules are intentionally small:
finite data and orders; scalar/matrix exchange; contextual finite words and color
insertion; independent semantic bridges; canonical cycles and feasible matchings;
and source-facing endpoints with exact regressions. The final source map below
lists the declarations needed to review the complete proof chain.

Gates 1 and 2 have compiled, including the order/indexed equivalence, position
swaps, matrix characterization and product closure. The natural recurrence has
compiled with coefficient nonnegativity and linearity. Its equality with the actual
coloring sum, the independent canonical-loop source bridge, and source positivity
are checked at `637112b`. Explicit cycle/matching and composition-sorted source
bridges are now also checked, through `MatchingExpansion.lean` and `Source.lean`. Finiteness of cycle displays is obtained first from the actual
maximal-cycle deletion equivalence by strict support induction; permutation
reconstruction is a subsequent independent bijection, not a finiteness assumption.
The helper `ExchangeMatrix.lean` specializes the finite-involution calculation
to actual boundary orders and proves the list/scalar characterization.

## Fixed endpoint contracts

For `h : Tuple k n` with `0 < n`, define the raw `loopColoringLLT h m`
independently. Define `naturalCyclicExpansion h : NEExpansion` by the explicit
matching sum, and `cyclicExpansion h` by `naturalCast`. The main theorem is

```text
xQShift m (loopColoringLLT h m) = evalElementary m (cyclicExpansion h)
```

for every `m`, including zero. The same expression must satisfy

```text
∀ d j, 0 ≤ (((cyclicExpansion h).coeff d).coeff j)
MvPolynomial.IsWeightedHomogeneous (fun t : ℕ+ => t.val) (cyclicExpansion h) k
```

The five checked public wrappers are `sortedLoopModel`, `positiveCycleExpansion`,
`positiveMatchingExpansion`, `elementaryCoefficientFormula`, and `ePositive`
in `VerticalStripLLT.Challenges.CyclicHessenberg`. None may assume a semantic
bridge, deletion identity, positivity, or desired expansion as input.

For a shape `d` of weighted degree `k` and ordinary degree `b`, the natural
coefficient is `q^(k-b)` times the sum of `(1+q)^A` over feasible matching
tuples of shape `d`. The coefficient of `q^j` counts marked ascent-event
subsets satisfying `j = (k-b) + selected.card`. The event retains its layer.

## Regression requirements

We include empty support (`1`), singleton (`e₁`), one identity layer (`e₁^k`),
the generic two-vertex formula, complete two-vertex layers
`(q+2)^(n-1)(e₁₁+q e₂)`, a complete three-vertex layer
`e₁₁₁+q(q+3)e₂₁+q²(q+2)e₃`, and Kim–Oh Example 6.7
`(q+2)e₁₁₁+q(q+2)e₂₁`. At `q=0` the result is the number of canonical
loop covers times `e₁^k`.

We also check the zero alphabet, decreasing ties, reverse events in later
layers, fixed points in cycle counts, and unequal boundary contexts.

## Build and audit route

The primary owns the sole project build slot. Per authorizes Laplace through
the host supervisor's project-selecting constrained bridge. Euler is reserved
for Fable; the RealRooted-only Lean MCP must not be used for this repository.
No local Lake, dependency update, toolchain change, bridge modification, cache
cleanup or SSH change is authorized by this task.

Host readiness and the pinned cache preparation are confirmed. Publish the task
branch and submit its full commit SHA with `--project VerticalStripLLT` and focused
`--target` builds; do not repeat cache preparation for this unchanged pin.
The host runs the pinned external-cache workflow in its own checkout,
serialized with other Laplace jobs. Source checkpoints submitted for compilation
are explicitly unverified until their receipts and logs are inspected.

The first focused targets are `VerticalStripLLT.CyclicHessenberg.Data`,
`VerticalStripLLT.CyclicHessenberg.BoundaryOrder`, and
`VerticalStripLLT.CyclicHessenberg.Kernel`. Later builds follow the gates above.
Final checks include the whole library and existing audit entry points.
Static guards reject `sorry`, `admit`, new axioms and `native_decide` in the
new subtree. Axiom queries must report at most `propext`, `Classical.choice`
and `Quot.sound`. Exact SHAs, job IDs and log locations belong in `HANDOFF.md`.

## Composition-source review decision

Astra independently approved the positive-composition source bridge. We use
Mathlib `Composition k`, ordered loop covers with an explicit first-boundary
permutation, and decreasing label lists inside each composition block. Color
choices are monotone positional words with exactly the prescribed positive
equality-run lengths. The source polynomial is defined directly from positional
ascent events and this independent run weight. A separate bijection with
increasing lists of distinct block colors must identify the run weight with
the source monomial quasisymmetric weight; this cannot be left as prose.
The cover/color bijection uses checked color-sort uniqueness.

## Final source map and independent integration review

We follow the manuscript proof strategy. The extra finite indexing, equality-run
and order lemmas expose its bookkeeping to Lean; they do not replace its argument.
Per reiterated this requirement during integration. Any mathematical change must
be justified by an improvement to the paper argument.

| Result | Checked declaration |
| --- | --- |
| Literal composition source with ordinary finite `M_β` | `cyclicLLT` in `Source.lean` |
| Run weight equals increasing-color `M_β` | `runMonomialQuasisymmetric_eq` |
| Exact source/coloring bridge | `cyclicLLT_eq_loopColoringLLT` |
| Layer product satisfies spectator-aware exchange | `naturalOpenKernel_exchangeCompatible` |
| Both independently fixed residual contexts | `ExchangeCompatible.prefixKernel`, `.suffixKernel` |
| Signed-to-positive root deletion | `signedRootDeletion_eq_rootDeletion` |
| Actual coloring recurrence | `weightedKernelColoring_insert_max` |
| Recursive expression equals coloring evaluation | `naturalKernelExpansion_eval_eq_weightedKernelColoring` |
| Canonical-cycle expansion | `naturalKernelExpansion_eq_cycleSum` |
| Cycle display/permutation equivalence, including fixed points | `cycleDisplayEquivPerm` |
| Explicit matching expansion | `naturalCanonicalCyclicExpansion_eq_matchingExpansion` |
| Source equality after one shift | `shift_cyclicLLT_eq_cyclicExpansion` |
| Forced coefficient factor | `naturalCyclicExpansion_coeff` |
| Finite marked-ascent cardinalities | `cyclicExpansion_coeff_eq_card_markedMatching` |
| Uniform coefficientwise positivity and degree | `Challenges.CyclicHessenberg.ePositive` |
| Closed loops/identity monodromy | `loopCoverMatchingEquiv` |

The independent Astra integration audit found no orientation or semantic defect.
It checked successive matching composition, the source-to-target boundary ratio,
fixed-point singleton cycles, positive block sizes, retained layer indices in
ascent events, and the exact coefficient equation `j = k-count + selected.card`.
The raw source, composition source and desired expansion have separate definitions.
No desired semantic equality or positivity theorem is assumed as a hypothesis.
The reviewed increasing-color equivalence and its weight theorem are now checked.

The formal source is the finite-alphabet composition formula from the manuscript.
The cyclic proof modules form their own dependency tree. `RepositoryAudit.lean`
loads existing results to test integration.

After Per reiterated the proof-strategy constraint, Astra compared the finalized
chain against the manuscript again and found no mathematical deviation or unmet
core theorem contract. In particular, `lengthSlice` is the finite homogeneous
coefficient extraction implicit in the manuscript's `R_d` comparison. Its
read-only review also confirmed the formal q=0 proof: only singleton-cycle
matchings survive, and `loopCoverMatchingEquiv` identifies their number with
canonical loop covers. This includes k=0 and the required zeroth power.
The final combined build checks these arguments and every planned regression.
`naturalCyclicExpansion_at_zero` gives the formal elementary-basis specialization;
`specialize_shift_cyclicLLT_zero` gives the independent finite-alphabet version.

## Verification receipts and reproducibility

- Final full library plus cyclic and existing public-result audits:
  `09b32d62b4a5fb9a0ef0e63fb2ef2505720cfd8d`, job
  `20261112T122307-ff9f3c03`, exit 0, 2496 jobs.
- Focused final q=0 and complete cyclic examples:
  `bcc016cd11112ea67ea8284c6ee2725689822ddd`, job
  `20261112T122136-a344882f`, exit 0, 1710 jobs.
- The expanded audit has 110 cyclic queries and an executable allowlist guard;
  the separate repository regression audit checks seven existing public results.
  No unexpected axioms occur. The guard prevents a truncated remote log from
  hiding an unexpected dependency.
- The full library and ordinary/circular example modules compile. The seven old
  endpoint queries are exposed through `CyclicHessenberg/RepositoryAudit.lean`
  because the bridge accepts library targets, not the root verification scripts.
- Static checks find no `sorry`, `admit`, added axioms, `native_decide`, unsafe
  declarations or kernel-check disabling. Source widths and `git diff --check`
  pass. No source-tree symlinks or generated dependency/build trees were added.

All required declarations and proofs are checked. Per authorized merging the
verified pull request.

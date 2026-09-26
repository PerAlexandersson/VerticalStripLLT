# VerticalStripLLT

Lean formalization of Per Alexandersson and Robin Sulzgruber,
*A combinatorial expansion of vertical-strip LLT polynomials in the basis of
elementary symmetric functions* (arXiv:2004.09198; published 2022).

The first objective is the ordinary, noncircular theorem. We use valid
Schröder step words and finite coloring sums in
`MvPolynomial (Fin m) (Polynomial ℤ)`, uniformly in the alphabet size `m`.
Formal elementary expressions have a separate evaluation homomorphism.
A general-purpose symmetric-functions library is outside the scope.

## Current verified slice

- The empty path has value `1`, and `ne` has value `e₁`, for every finite alphabet.
- `nde`, `nnee`, and `nene` decode to a strict edge, a normal edge, and no edge.
- For every valid path, normal and strict edge sets are disjoint and both
  have increasing endpoints. For arbitrary `k`, `column k` constructs `n d^k e`,
  with no normal edges and precisely consecutive strict edges; its admissible
  colorings are exactly the strictly increasing maps.
- `coloringLLT_column` proves `G_(n d^k e) = e_(k+1)` for every `k` and every
  finite alphabet. Its finite-subset bijection proof came from Aristotle and
  was ported by Luna and checked locally.
- `SchroderPath.concat` concatenates arbitrary valid paths. The raw path and
  edge scanners satisfy append and translation laws. `coloringLLT_concat`
  proves coloring multiplicativity for all paths and finite alphabets, by
  decomposing the graph, factoring each weight, and splitting the finite sum.
- `coloringSplitEquiv` and `sum_colorings_split_mul` split finite colorings and
  factor independent sums. Diagonal steps can be resolved into `ne` or `en`
  while preserving validity; the unchanged edge scanners are proved equal.
- `markedDiagonalEdge` locates the strict edge at a chosen diagonal step.
  `coloringWeight_unicellular_of_edges` proves the local weight relation from
  explicit edge-insertion hypotheses. `coloringLLT_unicellular` combines the
  proved edge identities to give the general relation for every valid `U d V`.
- `ColoringSwap.lean` provides the swap involution, its restricted-coloring
  equivalence, and vertex-monomial preservation for the upcoming bounce proofs.
- `SwapSum.lean` proves the restricted swap-sum identity under explicit edge
  symmetry hypotheses. `BouncePath.lean` and `PrefixScanners.lean` supply valid
  local step swaps and scanner decomposition at arbitrary prefix endpoints.
  `SecondBouncePath.lean` composes those swaps into the valid second successor.
  `FirstBounce.lean` now proves `coloringLLT_firstBounce`: the full
  `U nn V d e W` to `U nn V e d W` identity with factor q, uniformly in the
  finite alphabet. Its scanner, graph, and weight proofs are separate modules.
  `SecondBounce.lean` proves the second identity `U dn V de W` to
  `U nd V ed W`, using the same graph background and an interval-based
  coloring involution.
  `ThirdBounce.lean` proves the third single-bounce relation, constructs both
  valid successors, and uses explicit cancellation of q−1.
- `ColumnCharacterization.lean` proves the converse: every valid path with
  exactly one east step is a column. `FirstEast.lean` defines the total
  first-east height and identifies it with the prefix endpoint height.
- `firstEast_north_reduction` and `firstEast_product_reduction` package valid
  successors, strict measure decreases, and value identities for arbitrary
  invariants satisfying the recurrence. The diagonal-predecessor branch is open.
- `BounceSeed.trace` constructs a terminating prefix bounce trace while
  preserving the strict gap and exact return indices. `BounceTrace.decompose`
  retains the terminal pair in an indexed certificate; its `raiseFinal` lemma
  preserves the decomposition when a north precedes the final diagonal.
- `SatisfiesReductionRecursion.generalizedFirstBounce` proves the generalized
  NN bounce by strong induction on prefix length, with a valid successor and
  strict first-east-height decrease. Word evaluation, local recurrence
  adapters, successor validity, DD coordinates, and the linear DD step are
  separate modules. The DN and ND analogues now give all three generalized
  bounce reductions with valid successors and strict measure decreases.
  `firstEast_prefix_cases` supplies the exhaustive geometric case split;
  `SatisfiesReductionRecursion.unique` now proves uniqueness for that
  sufficient certificate by nested induction on size, east count, and height.
- The independent orientation expression is now defined using finite normal
  edge choices and highest-reachable-vertex fibers. HRV maximality and
  idempotence, fiber nonemptiness, and empty-path normalization are proved.
  `orientationExpansionAt_column` proves the column initial condition.
  `coloringLLT_column_eq_eval_orientationExpansion` identifies the independently
  defined coloring and orientation expressions for every column and alphabet.
  `orientationExpansionAt_concat` proves orientation multiplicativity, with
  separate orientation-splitting and HRV transport modules.
  `orientationExpansionAt_unicellular` proves the independent orientation
  unicellular identity. Transport, insertion sums, and shifted/unshifted
  specializations are separate modules.
  `orientationExpansionAt_firstBounce_general` proves the independent NN
  orientation bounce for unrestricted middle words and every parameter z.
  Its HRV transport, matching bijection, and sum assembly are separate modules.
  `qShift_orientationExpansion` proves that coefficient substitution q→q+1
  gives the independently defined shifted orientation expression.
- `SatisfiesReductionRecursion` adds two separately named leading-east bounce
  clauses for the reduction proof. Its coloring witness, generic third-bounce
  consequence, and ring-map transport are checked. The original restricted
  predicate stays unchanged; its exact uniqueness claim remains open.
- `coloringLLT_pair_unicellular` proves
  `G_nnee − G_nene = (q−1) G_nde` for every finite alphabet.
- In two variables, `coloringLLT_strictPair_eq_evalElementary_two` proves
  `G_nde = e₂`, and `coloringLLT_normalPair_eq_evalElementary_two` proves
  `G_nnee = e₁² + (q−1)e₂` by evaluating a separate formal expression.

The general column initial condition, multiplicativity, and general unicellular
relation and both single-bounce recurrence identities are proved.
`coloringLLT_satisfiesRecursion` bundles these facts with empty normalization
in a named recurrence predicate. The third single-bounce coloring relation is
also proved. All three generalized bounce branches are proved;
the DN orientation bounce identity and the full orientation/coloring semantic
bridge remain to be proved. `coloringLLT_eq_of_satisfiesReductionRecursion`
identifies any invariant with a proved sufficient certificate with the
coloring polynomial; the independent orientation certificate remains open.

## Build and verification

Pinned toolchain: Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; the dependency manifest is tracked.
In this Docker workspace, check that no other Lean/Lake build is active, then
run the following commands sequentially from the project root:

```bash
lake-workspace build VerticalStripLLT.SmallCases
lake-workspace build
lake-workspace env lean Verification.lean
```

The wrapper uses `/lake-cache/ai-projects` for dependencies and build output.
Its temporary external package override emits a packages-directory manifest
warning; do not run `lake update` in response. `Verification.lean` prints the
axioms of the public slice theorems. Only standard Lean axioms are expected;
the source contains no proof placeholders or custom axioms.

See [the reviewed formalization map](docs/FORMALIZATION.md) for source
correspondence, representation comparisons, termination measures, and precise
milestone boundaries. The author-supplied manuscript under `references/` is
immutable.

Later projects, including circular vertical-strip LLT polynomials and LLT
cumulants, should depend on this foundation rather than duplicate it.

See `HANDOFF.md` for current ownership and `AGENTS.md` for project workflow.

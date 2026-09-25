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
  edge scanners satisfy append and translation laws; coloring multiplicativity
  remains the next proof obligation.
- `coloringSplitEquiv` and `sum_colorings_split_mul` split finite colorings and
  factor independent sums. Diagonal steps can be resolved into `ne` or `en`
  while preserving validity; the unchanged edge scanners are proved equal.
- `coloringLLT_pair_unicellular` proves
  `G_nnee − G_nene = (q−1) G_nde` for every finite alphabet.
- In two variables, `coloringLLT_strictPair_eq_evalElementary_two` proves
  `G_nde = e₂`, and `coloringLLT_normalPair_eq_evalElementary_two` proves
  `G_nnee = e₁² + (q−1)e₂` by evaluating a separate formal expression.

The general column initial condition and the first local recursion case are
proved. Coloring multiplicativity, general unicellular and bounce relations,
recurrence uniqueness, a terminating recursive invariant, the orientation
formula, and the full semantic bridge remain to be proved.

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

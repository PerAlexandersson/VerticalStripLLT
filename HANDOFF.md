# VerticalStripLLT handoff

## Current task: full circular expansion

2026-09-26: user approved the circular/component plan and authorized
Aristotle plus Luna/Terra implementation. Latest steering: target the full
general statements; keep concrete examples under `VerticalStripLLT/Examples/`.
The main library imports no new example modules. Ordinary expansion is complete.
The general circular HRV expansion and flip-component theorem are not yet proved.

Verified circular foundations:

- `Circular.Diagram`, `Edge`, and `EdgeBounds`: cyclic area conditions,
  corner-restricted strict arcs, modular endpoints, and exclusion of loops.
- `Circular.EdgeData.coloringLLT`: direct finite coloring semantics, retaining
  distinct edge instances. `Diagram.coloringLLT` specializes it to circular data.
- `EdgeData.strictOrderEnumerator_eq_zero_of_not_admissible`: cyclic selected
  relations contribute zero.
- `EdgeData.xQShift_coloringLLT_eq_orientation_sum`: for any finite directed
  edge-instance graph and every alphabet, the shifted coloring sum is the
  q-weighted sum of strict order enumerators of acyclic selected relations.
- `acyclic_walk_injective`, `acyclic_walk_length_lt`, and
  `acyclic_lifted_walk_span_le`: arbitrary finite acyclic walks have at most
  n−1 edges and lift span at most (n−1)² under the natural step bound.

The general semantic identity is independent of HRV and recurrence. It does
not identify an individual selected-order enumerator with an HRV monomial.
Actual lifted HRV and its reachability characterization are now proved.
Next supply the circular local reductions, same-state no-wrap invariant, and
termination proof. `docs/CIRCULAR_REDUCTION_OBLIGATIONS.md` is a research note,
not a proved certificate. The weak/h versus strict/e passage is omega.

Verified foundation checkpoint `276bb93` and HRV checkpoint `1ea6877` are
pushed. Base/roots/example-isolation checkpoint `5f5bcba` is verified and
pushed. The HRV checkpoint proves `Orientation.isGreatest_liftedHRV`, `liftedHRV_translate`,
`residue_liftedHRV_eq_hrv`, weighted degree n, and nonnegative coefficients of
the independently defined `Circular.shiftedOrientationExpansion`.

Aristotle project `5835802e-8139-48b7-a07b-06add00f1f14`, task
`f726d73c-794d-4693-8a20-58660dab3545`, is active on the full circular
expansion statement with the checked prefix. Primary owns the live observer,
candidate audit, and all builds. Exact request: `docs/ARISTOTLE.md`.

All delegated files have returned. Primary owns all source, docs, integration,
and the sole build slot, including new `Circular/ComponentSemantics.lean`.
`StrictEdgeInjectivity`, `LiftCover`, and `Flip` pass focused checks. The flip
witness derives the exchanged edge memberships and distinctness, then ascent
invariance on complete global components. No general component identity is
assumed. Exact interfaces: `docs/CIRCULAR_FLIPS.md`.

Zero-area checkpoint `b7fe916` is verified and pushed. The full zero-area family is now proved by
`Circular.coloringLLT_shifted_eq_expansion_of_no_normal` in
`Circular/ZeroAreaExpansion.lean`: arbitrary n, D with no non-strict arcs,
and every alphabet. The proof derives finite chain orders on the actual HRV
fibers and constructs their coloring certificate; no certificate appears as
a hypothesis of the final theorem. Empty orientation types give zero on both
sides. Luna's read-only audit confirmed the statement and fiber semantics.
`CutOrder` and `ZeroAreaIncoming` are verified general geometry for future
cut transport; the final zero-area proof instead uses fiber orders directly.

A separate Aristotle request for that family was rejected by the concurrent
project limit and is now superseded by the local proof. No task was created
or canceled. The main full-expansion observer has had stream interruptions;
it was reconnected to the same task and the service remains in progress.
Its current mathematical obstacle is the all-corners-strict reduction, not
the proved zero-area base. No full circular equality is claimed.

## Ownership, delegation, and checks

Primary `/root` owns all returned source, strategy, integration, docs, and the
sole globally serialized local build slot. Luna implemented diagram/edge data
and ported the walk bounds. Terra implemented generic coloring and orientation
semantics and audited source fidelity. Both returned their assigned files and
remain build-free; no build-slot transfer occurred.

Aristotle completed subset expansion project
`40998e1f-04ed-473c-9d58-5656253cfa9d` and acyclic walk bound project
`8da2f9e8-2c92-4aaa-83a7-a88f6f36d257`. Both candidates are integrated and
locally checked, with unchanged requested statements. The projected-reachability candidate is also locally checked; its service
status was `COMPLETE_WITH_ERRORS` due to a malformed namespace wrapper,
repaired without changing the mathematical statement. Only the full circular
expansion request is active. Provenance is in `docs/ARISTOTLE.md`.

The component-foundation checkpoint passes the default full build and all
568 declarations in `Verification.lean`; only standard Lean axioms occur.
Source placeholder and 100-column guards pass. Logs under
`/lake-cache/ai-projects/build/VerticalStripLLT/`:
`circular-components-checkpoint-build.log`,
`circular-components-checkpoint-axioms.log`, and
`circular-components-focused.log`. The zero-area checkpoint checked 542. The previous base/roots checkpoint checked
517 declarations. No TeX compilation or local combinatorial enumeration was
run; all Luna/Terra tasks were build-free.

## Source and architecture

Independent Astra planning review preceded implementation. Architecture/source
map: `docs/CIRCULAR_FORMALIZATION_PLAN.md` (pushed planning checkpoint `00be22e`).
Exact targets/progress: `docs/CIRCULAR_GOALS.md`. Read-only source is Overleaf
`LLT flip/old-main.tex` with its editorial audit; sibling `main.tex` is empty.
The earlier `LLT-flips/llt-flips.tex` is background. Source hashes are recorded
in the plan; Overleaf and committed ordinary references remain unchanged.

## Completed ordinary expansion

The main ordinary Alexandersson–Sulzgruber expansion is proved in the reviewed
finite-degree model, for every valid path and every finite alphabet (including
zero). `Expansion.lean` exports:

- `coloringLLT_eq_eval_orientationExpansion`: the unconditioned semantic bridge.
- `coloringLLT_eq_orientation_sum`: the explicit ordinary orientation sum.
- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion` and
  `coloringLLT_shifted_eq_orientation_sum`: the q→q+1 formula.
- `coloringLLT_shifted_e_positive`: one elementary expression, uniform in the
  alphabet, with every integer q-coefficient nonnegative and weighted degree n.

`ExpansionStability.specializeTail_coloringLLT` (namespace VerticalStripLLT)
proves compatibility after setting any number of final variables to zero.
`OrientationDegree` proves HRV fiber sizes sum to n and weighted homogeneity.
`OrientationNatural` and `OrientationPositive` prove genuine coefficient
nonnegativity by a natural-coefficient lift of the same orientation sum.

The coloring and orientation expressions remain independently defined.
The proof uses their proved sufficient recurrence certificates and
`SatisfiesReductionRecursion.unique`, with nested strong induction on size,
east count, and first-east height. Generalized NN/DN/ND reductions return valid
paths with strict decreases. No recurrence or expansion assumption appears
on the main theorem. No recursive invariant was renamed LLT.

## Scope and boundaries

The finite-alphabet family, formal elementary coefficients, degree, and
specialization compatibility are the chosen interface to the ordinary
infinite-variable formula. No general symmetric-functions library was built.
Uniqueness for the original restricted `SatisfiesRecursion` remains a separate
unproved claim; the main proof uses the explicitly stronger certificate,
whose clauses are proved for both concrete models. This does not weaken the
main expansion statement. Circular and flip-component implementation remains
downstream; its newly requested plan is separate from the completed ordinary
scope. Cumulants are not part of either scope.

## Verification and checkpoint history

The completed source passes the default local build (1668 jobs) and all 438
axiom checks in `Verification.lean`. Only `propext`, `Classical.choice`, and
`Quot.sound` (or no axioms) occur. Global forbidden-source and 100-column
guards pass. Reference files are unchanged, both initialization commits are
ancestors, and no local package/build cache was created.

Logs under `/lake-cache/ai-projects/build/VerticalStripLLT/`:
`completion-full-build.log`, `completion-axioms.log`.
Earlier integration logs use prefixes `expansion-`, `uniqueness-`,
`generalized-bounces-`, and `orientation-nn-`.

- `81b4885`: independent Astra architecture review before scaffolding.
- `5a3b763`, `9a04105`: sufficient-certificate decisions before implementation.
- `de6026f`: orientation unicellular and indexed bounce geometry.
- `9d3574c`: generalized NN with valid successor and measure decrease.
- `d244170`: independent NN orientation bounce; 344 axiom checks.
- `6c1f8ab`: all generalized bounces, first-east cases, and shift.
- `91f5760`: sufficient-certificate uniqueness and coloring characterization.
- `a1f64c4` (pushed): DN orientation identity, independent recurrence
  certificate, main expansion, positivity, degree, and alphabet stability.

## Ordinary completion ownership and remote work (historical)

Primary `/root` owns all source, strategy, integration, documentation, and the
sole local build slot. All Luna/Terra assignments have returned and released
ownership. No active local build, nested Claude process, or remote proof job
remains. No build-slot transfer occurred.

Luna ported the DN orientation proof into seven helper modules plus the final
theorem and implemented bounded coefficient/certificate tasks. Terra audited
source fidelity and repaired the finite-subset stability argument. Primary
performed API/normalization repairs, semantic integration, stability transfer,
and all local verification. Final read-only audit confirmed arbitrary n/P/m,
correct q substitution, and full coefficient/degree scope.

Aristotle DN project `432e553c-fc15-4226-8795-9bc0b1786b28`, task
`fa04e12e-eb5d-43e6-ac50-92e432384704`, completed 2026-09-26 07:15:16 UTC.
The 142029-character supplied prefix and exact target statement are unchanged.
The integrated proof has no hidden no-east hypothesis. Requests/candidates:
`/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-second-bounce`.
All other completed remote provenance is in `docs/ARISTOTLE.md`.

Issues #1–7 are closed. Issue #7 records the completed orientation milestone:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/7.
The verified completion checkpoint is pushed and #7 is closed. No active
implementation task or mathematical blocker remains for the ordinary scope.
The newly requested circular/component planning task is recorded above.

## Environment and durable references

Only primary may invoke local Lean/Lake. Before EVERY invocation inspect global
Lean/Lake processes and defer if another build is active. Use `lake-workspace`,
reduced priority, and external caches; never plain Lake or lake update.
Lean v4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected. No `.lake/packages` or
`.lake/build` exists in the project. The repository remains private.

Push with invocation-local HTTPS rewriting and `gh auth git-credential`,
leaving configured remotes unchanged. Initialization `830cc6b` and `130f7e8`
are preserved; references remain unchanged from `130f7e8`.
`docs/COMPLETION.md` records the requirement/evidence audit.
`docs/FORMALIZATION.md` maps source statements and records architecture history.
`docs/COEFFICIENT_OBLIGATIONS.md` records the now checked finite-degree boundary.
The archived restricted-middle nonderivability candidate remains unverified
and unused; it does not refute the full recurrence or main theorem.

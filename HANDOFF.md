# VerticalStripLLT handoff

## Current checkpoint: neutral-bounce termination

2026-09-26: the user's contradiction lemma is proved in the explicit full-bounce
contact formulation, for arbitrary circular size and contact count. Ordinary
expansion remains proved; full circular expansion remains open.

Primary owns all returned source, strategy, integration, docs, and the sole
serialized build slot. Terra (`circular_colorings`) returned `StrictDepth`,
`PairedSwap`, `NeutralExchange`, and `NeutralContacts`; Luna (`circular_data`)
returned `NeutralRank`, `ParallelPaths`, `EdgeLength`, and `StrictEdgeEquiv`.
Primary integrated/repaired their candidates and wrote `NeutralTransport` and
`NeutralTermination`. Both bounded lanes are released and remained build-free.
Astra independently reviewed the full-DN proof and final hypothesis boundary.
No build-slot transfer occurred. Examples remain isolated.

Exact new declarations in `Circular/NeutralTermination.lean`:
- `FullNeutralBounce.preserves_acyclic`;
- `FullNeutralBounce.strictRank_lt`;
- `not_admissible_of_infinite_full_neutral_bounce`;
- `strict_cycle_of_infinite_full_neutral_bounce`;
- `coloringLLT_eq_zero_of_infinite_full_neutral_bounce`.

The last two locate a cycle in the initial strict graph and make its independent
coloring LLT zero for every finite alphabet. `FullNeutralBounce` records the full
DN contact paths, free endpoints, next-residue relation, and exact strict-edge
replacement. It does not assume separation, conjugacy, rank decrease, or LLT
identities. These structural conclusions are derived in Lean. The rank is
`Diagram.strictRank`, the sum of strict-ancestor depth at each edge head times
its natural circular length. The main path is two vertices longer than the
closed parallel component, proving disjointness. Exchanging the paths conjugates
the strict graphs; only the two endpoint lengths change, by +1 and -1, so rank
strictly decreases under acyclicity. An infinite natural descent is impossible.

Proof and source interface: `docs/proofs/NEUTRAL_BOUNCE_TERMINATION.md`.
Remaining interface: derive these contact data from a formal circular word-bounce
decoder. Normal edges are unconstrained by the contact structure; half-square
area preservation belongs to the actual DN word rewrite. The circular coloring
and HRV bounce identities and existence of a terminal/area-decreasing reduction
remain open. The neutral lemma does not establish the full circular expansion.
Next implement the word/contact correspondence, reusing ordinary bounce geometry,
then prove the circular semantic identities with the full periodic exterior.

Focused and default builds pass (1726 jobs). All 669 axiom checks pass with
only propext, Classical.choice, and Quot.sound. Source and 100-column guards
pass. Both initialization commits and reference files are unchanged. Logs: `neutral-termination-checkpoint-build.log` and
`neutral-termination-checkpoint-axioms.log` under the external build directory.
Verified source checkpoint: `28c5ba8`, following `d06e883`.
No TeX build, combinatorial enumeration, or new remote Aristotle job was run.
The previous Aristotle continuation returned no proof; the bounded local proof
and independent Astra review resolve this lemma without resubmitting that job.

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
Next supply the remaining circular local reductions and word/contact bridge;
the contact-level neutral termination proof is now complete. `docs/CIRCULAR_REDUCTION_OBLIGATIONS.md` is a research note,
not a proved certificate. The weak/h versus strict/e passage is omega.

Verified foundation checkpoint `276bb93` and HRV checkpoint `1ea6877` are
pushed. Base/roots/example-isolation checkpoint `5f5bcba` is verified and
pushed. The HRV checkpoint proves `Orientation.isGreatest_liftedHRV`, `liftedHRV_translate`,
`residue_liftedHRV_eq_hrv`, weighted degree n, and nonnegative coefficients of
the independently defined `Circular.shiftedOrientationExpansion`.

Aristotle project `5835802e-8139-48b7-a07b-06add00f1f14`, task
`f726d73c-794d-4693-8a20-58660dab3545`, was canceled after preserving its corner-reduction candidate. The candidate
left the all-corners-strict helper unproved. Primary has locally verified the
useful recurrences and an explicitly conditional reduction; no full circular
identity is claimed. Continuation task `b6cda868-d1f9-4ec9-a51c-f81bff3c6354` is now
`COMPLETE_WITH_ERRORS`: the returned continuation leaves the intended target
unproved and supplies a report rather than a proof. No new Lean proof was
imported. There is no active Aristotle task in this lane. See `docs/ARISTOTLE.md`.

Luna returned `Circular/StrictCycleVanishing.lean`; primary repaired and verified
it. Luna completed the read-only mathematical audit: acyclicity and strict-edge
injectivity alone do not give ordinary cut transport. Terra completed the
read-only corner audit and external continuation-prefix packaging. Both lanes
are released. Primary owns all repository files, requests, and the sole build slot.
The component checkpoint `386d6a7` is pushed (568 axiom checks).
The corner checkpoint `360c54a` is verified and pushed (613 axiom checks).

Corner reduction focused build passes (1400 jobs):
`Diagram.xQShift_coloringLLT_corner` and
`Diagram.shiftedOrientationExpansion_corner` are independent matching recurrences.
`expansion_of_cornerReduction` uses measure edge-count² + normal-edge-count.
`expansion_of_strictCorners_positive` isolates the exact remaining hypothesis:
all corners strict, strict relation acyclic, and at least one normal edge.
The strict-cycle and zero-normal branches are proved without certificates.
Both reduction theorems have explicit hypotheses; neither is the full bridge.


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
it was reconnected to the same task. After preserving `corner-checkpoint.lean`,
primary canceled the redundant base-case work to port the corner reductions
and resume with the now-proved base. Cancellation is not completion.
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
repaired without changing the mathematical statement. The original full circular
task is canceled; the narrowed continuation returned `COMPLETE_WITH_ERRORS`. Provenance is in `docs/ARISTOTLE.md`.

The corner checkpoint default build passes (1715 jobs); all 613 axiom
checks pass with only standard Lean axioms. Source and 100-column guards pass.
Logs: `circular-corners-checkpoint-build.log`,
`circular-corners-checkpoint-axioms.log`, and `circular-corner-reduction.log`. The root build briefly overlapped an external RealRooted
build after primary failed to stop on the process precheck; it finished in
about one second. Primary deferred the remaining audit until the slot clears
and now gates invocations on an empty process check. No external job was
stopped. This was a serialization mistake, not a build-slot transfer.

The earlier component-foundation checkpoint passes the default full build and all
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
`LLT flip/old-main.tex` with its editorial audit. The initial audit found
`main.tex` empty; it now contains the rewritten draft.
The earlier `LLT-flips/llt-flips.tex` is background. Source hashes are recorded
in the plan; old-main and committed ordinary references remain unchanged.
The user-authorized TODO addition to current main.tex is recorded below.

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

## Author clarification: use the draft's area recurrences

2026-09-26: author emphasized the ordinary-style area induction already outlined
in the draft. Primary and Terra rechecked R1/R2/R3/R4/R8; their ordinary branch
area drops are recorded in `docs/CIRCULAR_REDUCTION_OBLIGATIONS.md`. R3 is
neutral; the proposed secondary J rank addresses that case. Primary sent the
exact system and J/exterior-incidence guidance to the same active Aristotle
continuation via INSTRUCT (`RELATIONS_STEERING.md` externally). No Lean edits or
builds were needed for this clarification. The local identities still need
circular adapters and a full neutral-bounce progress proof; no component
transport theorem is needed for the aggregate circular induction.

## Current author clarification and Overleaf edit

2026-09-26: author chose geometric area (each strict corner counts as half a
square): A_geom = sum a_i - |S|/2. Use doubled geometric area in Lean when
needed. The author recalls that indefinitely continuing the forward neutral
bounce forces a strict directed cycle, and that Lilan may have a handwritten
proof. The contact-level version is now proved locally; see the current
checkpoint above for the precise interface and remaining word adapter.
A cycle entirely in one diagram's strict graph makes its entire LLT vanish;
a cycle using additional selected normal edges only kills that selected term.

At the user's explicit request, primary added a `\todo` to Overleaf
`LLT flip/main.tex` beside the strict-chain discussion (line 361). It states
relation (3), asks for the precise forward iteration and contradiction proof,
requires the cycle's strict edges to coexist in one reached diagram, explains
vanishing propagation along the identities, and notes Lilan's possible paper
proof. Existing old-main no-wrap TODO concerns the related selected-state gap.
After proving the contact lemma, primary updated the same TODO to request
manuscript incorporation and word/contact correspondence, with a Related Lean
comment linking the theorem and proof note. No other Overleaf content changed,
and no TeX build was run. The Overleaf directory has no Git repository.
Current main.tex SHA-256 after that update:
`f1c7be069cbd2c569576775b187a5a0f3b3782350f6d3ec515d5080098487a5f`.

## Continuation result and next action

Task `b6cda868-d1f9-4ec9-a51c-f81bff3c6354` on project
`5835802e-8139-48b7-a07b-06add00f1f14` returned `COMPLETE_WITH_ERRORS`.
Primary downloaded `continuation-result.tar.gz`, `returned-Continuation.lean`,
`returned-CONTINUATION_REPORT.md`, and `returned-ARISTOTLE_SUMMARY.md` under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-expansion/`.
The requested hard theorem still has its target placeholder. No returned
proof was imported. The report's suggestion that the ordinary theorem must
be formalized is about the isolated payload: it is already proved in this
repository and must be reused, not rebuilt. Reported numerical exploration
is not accepted as proof and was not integrated.

Primary owns all source/requests; edit lanes are released and no local build
is active. The explicit contact lemma is now proved. Next: derive its contact
data from the circular word procedure and port circular coloring/HRV bounce
identities using the existing ordinary implementation. Do not
resubmit the same broad target or the already proved zero-normal family.

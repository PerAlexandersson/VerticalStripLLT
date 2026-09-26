# VerticalStripLLT handoff

## Current task: circular and component formalization plan

2026-09-26: the user requested a downstream plan after completion of the ordinary
theorem. Primary `/root` owns `docs/CIRCULAR_FORMALIZATION_PLAN.md`, this handoff,
and the README planning link. Independent Astra reviewer
`/root/circular_plan_review` completed a read-only source/architecture review;
it owns no files. No circular implementation or build has started.

Planning source: Overleaf `LLT flip/old-main.tex` (its sibling `main.tex` is
empty), with `EDITORIAL-AUDIT.md`; the earlier `LLT-flips/llt-flips.tex` is
background. These sources and the committed ordinary references remain
read-only. The plan records source hashes, exact statement correspondence,
proposed declarations, milestones, and remaining proof obligations.

Priority is the aggregate circular HRV expansion, completing the manuscript's
lifted recurrence argument, followed by complete flip components. The user
expects the circular gaps to be fillable from the outline; components need
more detail. Weak/h versus strict/e is an omega translation, not a separate
mathematical obstruction. Keep the translation small and degree-local.

Next implementation milestone, beyond this planning task: finite circular
edge instances, admissibility, and the two-vertex circular coloring examples.
Primary retains the sole build slot; future bounded Luna/Terra/Aristotle tasks
must have explicit ownership and remain build-free locally.

Planning checks: source hashes rechecked against the files read; source/API
correspondence reviewed; `git diff --check` passed. References are unchanged
from `130f7e8`, and both initialization commits remain ancestors. No Lean,
Lake, TeX, or enumeration commands were run for this task. The documentation
checkpoint is titled `Plan circular HRV and complete flip-component formalization`.

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

## Ownership and remote work

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

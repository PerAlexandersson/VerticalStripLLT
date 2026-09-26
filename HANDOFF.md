# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
No external blocker applies. The authoritative reference files are immutable.

The independently defined coloring polynomial satisfies both
`coloringLLT_satisfiesRecursion` and the stronger reduction certificate.
All three single-bounce coloring identities are checked.
The independent orientation expression has checked empty, column, product,
unicellular, and unrestricted NN bounce identities. In particular,
`orientationExpansionAt_firstBounce_general` holds for every middle V and
parameter z, with multiplier C(z+1). Its eight-module Aristotle port uses
actual HRV/fiber bridges and a proved matching bijection; Terra independently
passed its fidelity audit. Ordinary and shifted specializations are checked.
`qShift_orientationExpansion` now proves coefficient substitution q→q+1
maps the ordinary expression to the separately defined shifted expression.

The arbitrary-length NN, DN, and ND bounce reductions are checked:
`SatisfiesReductionRecursion.generalizedFirstBounce`,
`generalizedSecondBounce`, and `generalizedThirdBounce`. Each returns valid
successor paths, equal east counts, and strict first-east-height decreases.
The DN and ND strong inductions are in separate word modules; their valid-path
packages are in `GeneralizedSecondBounceReduction` and
`GeneralizedThirdBounceReduction`. They use the checked linear `dd_step` with
ordinary and raised children, preserving BOTH diagonals in DD flattening.
`firstEast_prefix_cases` supplies the exhaustive return/north/bounce-seed split.

The stronger `SatisfiesReductionRecursion` explicitly adds both NN and DN
leading-east clauses to the unchanged manuscript-facing `SatisfiesRecursion`.
Do not claim restricted-recursion uniqueness or assume an orientation witness.
Uniqueness, the independent DN orientation identity, the full recurrence
bundle, and arbitrary-path coloring/orientation equality remain open.
The column semantic bridge is already checked for every finite alphabet.
Positivity, weighted degree, and alphabet stability remain distinct obligations.

## Verification and checkpoints

- `81b4885`: independent Astra architecture review before scaffolding.
- `5a33ef9`: uniform column orientation formula and coloring bridge.
- `5a3b763`: stronger sufficient-certificate route before implementation.
- `4d136c7`: orientation product and generic single ND reduction.
- `9a04105`: DN leading-east clause decision before implementation.
- `de6026f`: orientation unicellular and indexed bounce geometry.
- `9d3574c`: generalized NN with valid successor and measure decrease.
- `d244170` (pushed): independent NN orientation bounce; 344 axiom checks.

Current integrated generalized-bounce/shift batch: default build 1479 jobs,
355 public axiom checks, only `propext`, `Classical.choice`, and `Quot.sound`
(or no axioms). Source/100-column guards, immutable references, initialization
ancestry, and external-cache checks pass. Logs under
`/lake-cache/ai-projects/build/VerticalStripLLT/`:
`generalized-bounces-full-build.log` and `generalized-bounces-axioms.log`.
The NN orientation checkpoint logs use prefix `orientation-nn-`.

## Live work and ownership

Primary `/root` owns strategy, integration, all shared documentation, aggregate
imports/verification, and the sole local build slot. All returned port,
shift, and generalized-bounce modules are now primary-owned.

- `bounce_audit` (Terra): returned uniqueness API notes without a candidate.
  No missing mathematical branch identified; full induction remains primary work.
  Next owns only `BounceAgreement.lean`, a smaller seed-branch agreement lemma
  under agreement on same-size/same-east-count paths of smaller height.
  Build-free; no other file ownership.
- `path_invariants` (Luna): released port/specialization/DN-wrapper ownership.
- `column_paths` (Luna): released shift ownership. Its earlier inadequate DN
  single-bounce wrapper was replaced by the genuine checked Terra induction.

Aristotle DN project `432e553c-fc15-4226-8795-9bc0b1786b28`, task
`fa04e12e-eb5d-43e6-ac50-92e432384704`, accepted 2026-09-26 06:55 UTC.
Last observed IN_PROGRESS, 6 percent, updated 07:01:59 UTC. Observe this same
job; do not resubmit. Its isolated request directory is
`/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-second-bounce`.
Target: `orientationExpansionAt_secondBounce_general`, unrestricted V and z,
no multiplier. Supplied inputs reuse the locally checked NN helpers and DN
path/graph identities. Provenance and completed NN job IDs: `docs/ARISTOTLE.md`.

Issues #1–6 are closed; #7 tracks orientation bounce/certificate:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/7.

Next: verify Terra's uniqueness candidate, then port/check the remote DN
orientation proof when it returns. Assemble the independent orientation
certificate and transport it through `evalElementary` to obtain the coloring
semantic bridge by uniqueness. No recursive object is identified with LLT
merely by definition. Shifted positivity and degree/stability follow later.

## Build discipline and environment

Only primary may invoke local Lean/Lake. Before EVERY invocation inspect global
Lean/Lake processes; defer if another build is active. Use only
`lake-workspace`, reduced priority, and external caches. Delegates are build-free.
No build-slot transfer has occurred; no nested Claude process is active.

Lean v4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected; never run lake update or
plain Lake. No `.lake/packages` or `.lake/build` exists in the project.
Push with invocation-local HTTPS rewriting and `gh auth git-credential`,
leaving configured remotes unchanged. Initialization commits `830cc6b` and
`130f7e8` are preserved; references are unchanged from `130f7e8`.
Aristotle uses isolated4.28 snapshots; local builds remain authoritative.
Keep requests/candidates outside the checkout; require project/task receipts.

`docs/FORMALIZATION.md` maps declarations to the source; `RECURSION_PLAN.md`
records exact uniqueness assembly. `COEFFICIENT_OBLIGATIONS.md` records shift,
positivity, weighted-degree and stability boundaries. Other architecture notes:
`BOUNCE_TRACE_PLAN.md`, `ORIENTATION_MODEL.md`, `REDUCTION_CERTIFICATE.md`.
The older restricted-middle search ended COMPLETE_WITH_ERRORS. Its bounded
nonderivability candidate is neither locally verified nor imported and does
not refute the full recurrence; see `RESTRICTED_BOUNCE_AUDIT.md`.

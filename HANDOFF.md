# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
The coloring polynomial satisfies `coloringLLT_satisfiesRecursion`; all three
single-bounce coloring identities are independently checked.

The independent orientation model now has empty, column, product, and
unicellular identities: `orientationExpansionAt_empty`,
`orientationExpansionAt_column`, `orientationExpansionAt_concat`, and
`orientationExpansionAt_unicellular`. `OrientationSpecializations` supplies
ordinary/shifted product and unicellular corollaries. The last identity comes
from Aristotle, ported by Luna and checked locally without changing any
semantic definition. Equal-normal-edge transport, insertion sums, and the
final identity occupy three separate modules.
`coloringLLT_column_eq_eval_orientationExpansion` remains the uniform column
bridge for all finite alphabets; arbitrary-path equality is still open.

`SatisfiesReductionRecursion` explicitly adds BOTH NN and DN leading-east
clauses to the unchanged manuscript-facing `SatisfiesRecursion`. Its coloring
witness, generic single ND consequence, and ring-map transport are checked.
`coloringLLT_secondBounce_general` supplies unrestricted-middle DN semantics;
the existing restricted theorem is now its corollary with unchanged statement.
The DN extension was recorded in `9a04105` before implementation, following
primary/Terra audit of manuscript `LLTe_1`.

Word geometry is modular and checked: `BounceSeed.singleBounce_coordinates`,
`BounceTrace.decompose`, `BounceDecomposition.word_eq`, `parts`, and
`raiseFinal`. DD flattening retains TWO diagonals. Raising the final diagonal
by an inserted north preserves the terminal pair and trace conditions.
`SatisfiesReductionRecursion.generalizedFirstBounce` now proves the NN
relation for arbitrarily long bounce traces, returns a valid successor, and
certifies unchanged east count and strictly smaller first-east height.
Its strong induction uses both ordinary and raised child prefixes. The shared
`dd_step` proves the linear DD diagram for two terminal replacements.
Generalized DN/ND, uniqueness, the full orientation recurrence bundle, and the
arbitrary-path semantic bridge remain open.

## Verified checkpoints

- `81b4885`: independently reviewed architecture before scaffolding.
- `5a33ef9`: uniform column orientation formula and coloring bridge.
- `5a3b763`: sufficient-certificate route recorded before implementation.
- `4d136c7`: orientation multiplicativity and generic single ND reduction.
- `9a04105`: additional DN clause decision before implementation.
- `de6026f` (pushed): orientation unicellular and indexed bounce geometry.

Full/default build: 1463 jobs. All 259 public axiom checks pass, using only
`propext`, `Classical.choice`, and `Quot.sound`. Source and 100-column guards,
reference/initial-commit preservation, and external-cache checks pass.
Logs under `/lake-cache/ai-projects/build/VerticalStripLLT/`:
`generalized-nn-full-build.log` and `generalized-nn-axioms.log`.

## Live work and next action

Issues #1–6 are closed. Issue #7 tracks the orientation bounce identities and
recurrence certificate:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/7.

Aristotle NN project `5546ba1c-a34c-4605-9485-a4e42436e5bd`, task
`5964d41a-b920-4466-9490-fcc39d4de751`, completed 2026-09-25 21:13 UTC.
Its candidate proves `orientationExpansionAt_firstBounce_general` with
unrestricted middle V and multiplier `C(z+1)`. The supplied input prefix is
byte-for-byte unchanged. It has seven helper groups plus the final theorem,
about 1170 new lines. Candidate source is at
`/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-first-bounce/completed-candidate.lean`.
It has NOT yet passed local verification; no active Aristotle job remains.
Provenance is in `docs/ARISTOTLE.md`. The earlier unicellular job is integrated.

Next: port and check the NN orientation modules, then submit the isolated DN
orientation target using the resulting checked HRV/permutation API. In parallel,
adapt the checked generalized NN strong induction to DN and ND using `dd_step`.
The valid-word adapter and third-bounce wrapper are already checked; do not
unfold the zero-on-invalid-word convention inside recurrence arguments.
Finish the exhaustive first-east reduction and lexicographic uniqueness,
then transport the independently proved orientation certificate through
`evalElementary`. Shifted positivity and degree/stability remain requirements.

## Ownership and build discipline

Primary `/root` owns strategy, integration, shared docs, all source, and the
sole local build slot. All subagent ownership is returned and released.
Luna supplied word adapters, prefix geometry, and measure candidates; Terra
supplied the linear DD diagram. Primary completed the path normalization,
terminal validity, coordinate transport, and NN strong-induction integration.
No local Lean build or nested Claude process is active. Record new disjoint
ownership before assigning the orientation port or generalized DN work.

Before each local invocation inspect Lean/Lake processes globally. Use only
`lake-workspace`, with reduced priority and external caches. Record disjoint
ownership before new bounded tasks; Luna remains build-free. Authorized
Terra/Claude audits and remote proof searches may run in parallel.

## Source obligations and environment

`docs/FORMALIZATION.md` is the source map; `RECURSION_PLAN.md` records measures.
`BOUNCE_TRACE_PLAN.md`, `ORIENTATION_MODEL.md`, and `REDUCTION_CERTIFICATE.md`
record the current decomposition and independently proved semantic route.
Do not rename the stronger predicate, assume its orientation witness, or claim
original restricted-recursion uniqueness is proved.

The earlier restricted-east-middle search ended `COMPLETE_WITH_ERRORS`.
Its separate bounded nonderivability candidate is archived and read-only
reviewed but not locally verified/imported. It does not refute full recurrence
or the manuscript elementary specialization. See `RESTRICTED_BOUNCE_AUDIT.md`.
No external blocker applies; substantial proof obligations remain.

Initialization `830cc6b`, `130f7e8` and architecture `81b4885` are preserved.
Reference files are unchanged from `130f7e8`; never edit them. Lean v4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The wrapper package-dir
warning is expected; never run lake update or plain Lake. No local
`.lake/packages` or `.lake/build` exists. Push through invocation-local HTTPS
rewriting and `gh auth git-credential`; leave configured remotes unchanged.
Aristotle uses isolated 4.28 snapshots; local checks remain authoritative.
Only one remote job has been accepted concurrently. Require project/task IDs,
not just exit zero. Keep requests/candidates outside the checkout.

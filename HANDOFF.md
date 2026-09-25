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
No generalized-bounce value theorem, uniqueness, full orientation recurrence
bundle, or arbitrary-path semantic bridge is claimed complete.

## Verified checkpoints

- `81b4885`: independently reviewed architecture before scaffolding.
- `5a33ef9`: uniform column orientation formula and coloring bridge.
- `5a3b763`: sufficient-certificate route recorded before implementation.
- `4d136c7`: orientation multiplicativity and generic single ND reduction.
- `9a04105`: additional DN clause decision before implementation.
- Current source batch: orientation unicellular and indexed bounce geometry.

Full/default build: 1454 jobs. All 235 public axiom checks pass, using only
`propext`, `Classical.choice`, and `Quot.sound`. Source and 100-column guards,
reference/initial-commit preservation, and external-cache checks pass.
Logs under `/lake-cache/ai-projects/build/VerticalStripLLT/`:
`unicellular-geometry-full-build.log` and `unicellular-geometry-axioms.log`.

## Live work and next action

Issue #6's orientation initial/product/unicellular acceptance criteria are
verified. All earlier issues #1–5 are complete.

Active Aristotle project: `5546ba1c-a34c-4605-9485-a4e42436e5bd`.
Task: `5964d41a-b920-4466-9490-fcc39d4de751`, confirmed `IN_PROGRESS` (3%).
Target: `orientationExpansionAt_firstBounce_general`, unrestricted middle V
and parameter z, multiplier `C(z+1)`. Twenty-five checked modules plus the
relevant manuscript NN proof/table are supplied. The changing strict edge
requires real HRV analysis; no HRV preservation or semantic equality is assumed.
Observe this same job; do not restart because an observer expires.
Request receipts and directories are recorded in `docs/ARISTOTLE.md`.

The unicellular job `17bb2b30-57ab-40bf-b054-9640ec896ffc`, task
`188a6fed-48fe-4246-99e8-26055f8683ba`, completed and is integrated. Its only
supplied-proof edit was a 4.28 normalization repair, not imported locally;
all supplied statements and definitions are unchanged.

Next: inspect/port the NN orientation result, then handle DN and bundle the
orientation recurrence. In parallel, use indexed bounce decomposition to
construct valid generalized transformations and their value identities,
then prove uniqueness with measure `(size, eastCount, firstEastHeight)`.
Transport the orientation certificate through `evalElementary`, with
cancellation proved in the target ring, to reach the unconditional expansion.
Shifted positivity and degree/stability remain further requirements.

## Ownership and build discipline

Primary `/root` owns strategy, integration, all source files, shared docs,
and the sole local build slot. All Luna/Terra assignments are returned and
released. `path_invariants` ported the orientation modules/corollaries and
certificate edits; `column_paths` drafted the word geometry; `bounce_audit`
provided read-only source reviews. Primary repaired dependent normalization
and completed the raised-final closure proof. No local Lean build or nested
Claude process is active. The remote Aristotle task above remains active.

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

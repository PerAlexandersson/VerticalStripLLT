# VerticalStripLLT handoff

## Active continuation: circular coloring–HRV equality

The full circular theorem remains open. The checked outer induction has one
explicit input, `InteriorNDInductionStep`. Ordinary expansion, first-contact
interior overlap, direct/root-alias/separated ND, and complete NN/DN are proved.
Strict cycles make both actual models vanish; overlapping offset contact tracks
alone do not form a cycle. No flip work is active.

The active route constructs a smaller diagram by reversing the columns of the
merged strict component. Both its validity and strict doubled-area decrease
were verified at `e2f3479`. Its actual strict graph and positive integer lifts
are now proved to be transported by the reversal. Exterior normal-edge
transport, sink order and semantic assembly remain. Exact formulas are in
`docs/proofs/CIRCULAR_COLUMN_REVERSAL.md`.

The user's one-bounce strategy remains the surrounding reduction. Do not assume
termination of every arbitrary DD/DN/R1 rewrite sequence. The earlier ordinary
paired-child route uses a shorter-prefix induction for its raised child, not
smaller area; see `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.

## Current checkpoint: actual strict lifted transport

Five new modules provide the next geometric bridge:

- `ColumnDisplacement`: column lengths, predecessor coordinates and
  `columnDisplacement_pred_eq_drop`. The quotient is taken in naturals before
  casting into integers.
- `InteriorReversalHeads`: `reversalHeads_eq_image` and the old/new source images.
- `InteriorReversalDisplacement`: `reversalArea_reversed_length`, including the
  old-source correction and justified natural subtraction.
- `InteriorReversalLift`: the involutive periodic integer permutation
  `reversalLift`, with `reversalLift_residue` and `reversalLift_add_period`.
- `InteriorReversalStrict`: `strictAt_reversalLift_iff`, the exact integer
  equality `boundary_reversalLift_of_strictAt`, and
  `liftStep_empty_reversal_iff` for the actual strict lifted graphs.

All conclusions are derived from `InteriorMergedComponent K`; no target
transport or polynomial identity is assumed. Independent Astra source review
found no semantic defect. Focused build passed (1494 jobs), then full default
build passed (1896 jobs). All 1982 axiom-inventory declarations use only
`propext`, `Classical.choice`, `Quot.sound`. Source guards, 100-column limit
and whitespace checks pass.

Luna supplied head-set candidates; Terra supplied arithmetic candidates.
Primary corrected APIs, completed displacement arithmetic, constructed the
integer lift and proved strict transport. Only primary ran local builds.
The global build slot was temporarily occupied by RealRooted; no overlap occurred.

## Ownership and verification

All delegate edit lanes are released. Primary owns all integration and the sole
local build slot. No build-slot transfer occurred. Use only `lake-workspace`,
check for other Lean/Lake processes before each invocation, and keep generated
outputs outside the checkout. Lean MCP still targets RealRooted, so it is not
used to start implicit checks of this project.

External logs under `/lake-cache/ai-projects/requests/VerticalStripLLT/`:
`interior-reversal-transport-build.log`,
`interior-reversal-transport-full-build.log`, and
`interior-reversal-transport-axioms.log`.

Earlier detailed checkpoints and ownership history are retained in
`docs/archive/circular-interior-checkpoints-through-e2f3479.md` and Git.
Initialization commits `830cc6b`, `130f7e8` and immutable manuscript references
remain preserved. No Overleaf edits in this continuation.

## Aristotle provenance

The renewed full interior request is IN_PROGRESS in the existing project
`65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, new task
`a430cbfd-eb82-4070-b9c2-002ae875cb53`. Earlier direct observers lost their
connections while authoritative status remained active. Native session
**50277** now runs the externally stored
`circular-interior-with-chain-base/observe-existing-task.sh`. It rechecks
authoritative status after disconnections and reconnects only to this task;
it has a two-hour observation allowance and never submits, cancels or downloads.
Current output is `observer-follow.log`, with `observed-status.log` for the
latest authoritative status. A watcher timeout is not task termination.
After completion explicitly download the project archive into
`circular-interior-with-chain-base/result.tar.gz`.

Input source is `5266faa`, 200 modules and 21658 Request lines. The exact
unchanged target, source hashes, compatibility provenance and proof-route notes
are retained in that external directory. Independent Astra review checked the
target against `InteriorNDInductionStep`, dependency order and exactly one final
placeholder. No old unfinished helper was included. The new semantic base,
first-contact proof and zero-row invariants are inputs; the n=8 counterexample
and other failed shortcuts are explicit. Eight-file submission was rejected
before task creation; corrected five-file continuation succeeded. No duplicate.

Chain-singleton project `004c658b-1194-4c5c-be93-a3799e73d7be`, task
`40bf20a6-93f3-4fcb-8500-8739c2c8b234` finished COMPLETE.
External directory `circular-chain-singleton-expansion/` retains
`result.tar.gz`, `returned-Request.lean`, `returned-ARISTOTLE_SUMMARY.md`,
`review-prefix.diff` and exact input provenance from source `4cb8f5d`.
Final Request SHA256:
`62e8fc34bdca36232bddbd665e8d36916306f7a3c0f71a33ec246c098d9560a9`.
The review snapshot equals the final return. Only the appended proof was ported.
The returned prefix added one already-existing normal-edge compatibility lemma;
no definitions or hypotheses changed, and no remote prefix was imported locally.
Remote Lean4.28 compilation was auxiliary; local Lean4.34 checks are authoritative.

The older interior-overlap project `65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, task
`c4f22d47-e2f8-4545-9ba5-9edb35be49e9`, finished COMPLETE_WITH_ERRORS. Its full
interior target retains one sorry and was excluded. The completed explicit
restart and first-contact proofs were integrated at `4cb8f5d`. Do not poll
that task as live or treat its finite experiments as a general proof.
See `docs/ARISTOTLE.md` for earlier completed requests.

## Next proof obligations

Prove that outside boundaries avoid interiors of moved columns, and that
reversal preserves order between distinct lifted columns and fixed outside
points. For exterior endpoints, apply order preservation to x<y<x+n to retain
positive edge lengths below one period. The checked strict boundary equality
handles component strict heads; the old nonstrict source requires its separate
boundary threshold formula. Outside heads keep their boundaries unchanged.

Then transport every exterior normal edge, and the order of integer sinks.
Erase internal normal edges using the existing forced/descent factor APIs,
apply `OrientationSumConjugacy` and coloring relabeling to the residual graphs,
and cancel the nonzero common coefficient using the smaller target's IH.
No inequality between the two forced-edge counts is required.

Finally discharge `InteriorNDInductionStep`, instantiate the checked outer
induction and transfer HRV positivity/degree to the coloring polynomial. The
full theorem must include all finite alphabets without a recurrence hypothesis.

Aristotle's existing full interior task was authoritatively rechecked as
IN_PROGRESS during this continuation. It predates the column-reversal route;
do not claim that it has these new modules. No duplicate request was submitted.

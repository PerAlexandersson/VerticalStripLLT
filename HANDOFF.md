# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
The coloring-defined finite-variable polynomial satisfies the full normalized
recurrence predicate: `coloringLLT_satisfiesRecursion`. Independently checked
clauses are `coloringLLT_column`, `coloringLLT_concat`,
`coloringLLT_unicellular`, `coloringLLT_firstBounce`, and
`coloringLLT_secondBounce`, uniformly in every finite alphabet.

`coloringLLT_thirdBounce` now additionally constructs both valid successors
and proves the third single-bounce relation. It uses a separately proved
`coloringLLT_firstBounce_general` with arbitrary middle words and explicit
q−1 cancellation. The independent finite orientation expression is now defined,
with HRV maximality/idempotence, fiber nonemptiness, and empty normalization.
`orientationExpansionAt_column` proves its strict-column value for any ascent
parameter. `coloringLLT_column_eq_eval_orientationExpansion` is the complete
bridge for every column and every finite alphabet.
`BounceSeed.trace` constructs the terminating prefix geometry certificate.
No recursive invariant, uniqueness theorem, orientation recurrence bundle,
or full semantic bridge is assumed or claimed complete.

Recent source checkpoints, all pushed on private `main`:

- `91bee5f`: converse column classification and first-east height API.
- `275fb72`: second bounce and the normalized coloring recurrence bundle.
- `c75046c`: valid word reductions and recurrence transport through ring maps.
- `2aad0c1`: third single-bounce coloring relation.
- `4d57097`: generic product and north-predecessor reduction certificates.
- `73e8183`: orientation/HRV model and terminating bounce trace.
- `5a33ef9`: uniform orientation column formula and coloring bridge.

Column bridge checkpoint: full/default build (1436 jobs), all 176 public axiom
checks, source guards,
line-length checks, `git diff --check`, and immutable-reference checks pass.
Only standard Lean axioms occur. Logs:

- `/lake-cache/ai-projects/build/VerticalStripLLT/column-bridge-full-build.log`
- `/lake-cache/ai-projects/build/VerticalStripLLT/column-bridge-axioms.log`

## Live work and next action

Issues #1–5 are completed. Issue #6 tracks the orientation initial, product,
and unicellular identities; its column criterion is complete:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/6.

Aristotle project `09862def-0239-41ee-a563-b12536df8d1f`, task
`1d8ce50d-cbb5-44fb-9f5a-a6680f35a163`, is terminal `COMPLETE_WITH_ERRORS`.
The requested generic implication remains unproved. Its archive contains a
candidate bounded nonderivability theorem through size four; Terra is auditing
it read-only. This does not give a global counterexample. See the remote ledger.

Aristotle project `1d37e685-a581-4682-9b48-08fdcd5f3be6`, task
`d1be4127-7c06-4481-b02c-2da410c82198`, is confirmed `IN_PROGRESS` on
`orientationExpansionAt_concat`, using checked graph identities and exact HRV
semantics. Observe this same job; do not restart because an observer expires.

Next: prove orientation multiplicativity and the unicellular relation. In parallel, turn the terminating bounce trace into
valid generalized-bounce transformations. The restricted generic nd value
step remains open after the terminal unsuccessful Aristotle search. The
reviewed sufficient-certificate route is `docs/REDUCTION_CERTIFICATE.md`;
its additional semantic field must be proved for both models. Terra's corrected
trace uses a decreasing prefix word with its own strict gap.

## Ownership and build discipline

Primary `/root` owns strategy, integration, and the sole project build slot.
Build-free ownership for this continuation:

- `column_paths`: returned `HRVCongruence.lean`; primary owns integration.
- `path_invariants`: owns `OrientationInsert.lean` again for fixes from the focused build.
- `bounce_audit`: read-only audit of the terminal Aristotle bounded candidate.

Primary owns all other files. No local Lean build is active.

Keep all local builds serialized globally. Inspect running Lean/Lake processes
before each invocation; use `lake-workspace` with reduced priority. Never use
plain Lake or change dependencies to fit a remote candidate.

The user requests modular code, sparse/batched compilation, and bounded
parallel delegation to Aristotle and smaller Claude/Luna/Terra models.
Luna remains the default implementation worker, build-free. Record disjoint
file ownership here before every new assignment. Primary runs authoritative
local checks and pushes coherent verified checkpoints.

## Checked supporting modules and open proof obligation

`WordCounts`, `ColumnCharacterization`, `FirstEast`, and `NonemptyPath`
provide count/endpoint formulas, the one-east column converse, the total
first-east height and its endpoint meaning, and east-step existence for
positive-size paths. `NorthEastReduction` constructs the valid contraction
and swap and proves their east-count/first-east-height changes. `PathSplit`
constructs valid prefix/suffix paths at a diagonal return, translating the
suffix to the origin. `RecursionMap` transports all recurrence fields through
a ring homomorphism. Exact declarations and remaining decreases are in
`docs/RECURSION_PLAN.md`.

All three single-bounce proofs have separate path/scanner, graph, and
weight/algebra modules. Their semantic identity statements are in
`FirstBounce`, `SecondBounce`, and `ThirdBounce`. `Recursion` defines the
faithful restricted predicate; `ColoringRecursion` proves its coloring witness.
The durable source map is `docs/FORMALIZATION.md`.

`docs/RESTRICTED_BOUNCE_AUDIT.md` records a generic proof obligation: the
source's displayed third-bounce derivation invokes a first-bounce instance
with middle eV, outside the restricted recurrence. Terra and Claude Sonnet
independently checked the local diagram. This does not establish a global
counterexample or nonimplication. Primary rejected Sonnet's unsupported
stronger claim and speculative extra-bounce route. Do not silently strengthen
`SatisfiesRecursion` or claim generic uniqueness from the concrete coloring
proof. Its unrestricted first-bounce helper is proved independently.

Both read-only Claude audits completed successfully; no nested Claude process
remains active. Their external directories are `recursion-audit/` and
`restricted-bounce-audit/`. No external blocker applies.

## Environment

Initialization commits `830cc6b`, `130f7e8` and reviewed architecture `81b4885`
are preserved. Reference files are unchanged from `130f7e8`. Do not edit them.
Lean is `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected; never run `lake update`.
No local `.lake/packages` or `.lake/build` exists; dependencies/builds live
under `/lake-cache/ai-projects`.

Use invocation-local HTTPS rewriting plus `gh auth git-credential` to push;
SSH authentication is unavailable, and configured remotes must stay unchanged.
Lean MCP defaults to RealRooted: use explicit-root read-only searches and local
wrapper checks. Aristotle uses isolated Lean/Mathlib 4.28 snapshots; local
4.34 verification is authoritative. Never expose credentials or upload the
workspace/reference snapshot wholesale.

Previous goal turn and this continuation both made verified proof progress.
The full ordinary expansion remains unfinished; no completion/blocking audit
has been claimed. Older inventories and history are archived under
`docs/archive/` and preserved in Git.

Aristotle rejected the independent orientation-column submission because the
account already has the maximum number of active projects. No new project was
created. The exact checked request is prepared under external `orientation-column/`.
Keep the existing generic bounce job; Luna implemented the column locally,
and primary verified it. Do not resubmit the now-completed column target.
This service capacity limit does not block local proof progress.

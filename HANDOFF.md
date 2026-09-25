# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
The coloring polynomial satisfies `coloringLLT_satisfiesRecursion`, and all
three single-bounce coloring identities are checked independently.

The independently defined orientation expression has checked empty and column
values and multiplicativity: `orientationExpansionAt_empty`,
`orientationExpansionAt_column`, and `orientationExpansionAt_concat`.
`coloringLLT_column_eq_eval_orientationExpansion` proves the full bridge for
all columns and all finite alphabets. Orientation splitting, ascent counts,
reachability/HRV transport, and fiber factorization live in separate modules.
`HRVCongruence`, `OrientationInsert`, and `OrientationInsertStep` supply checked
fresh-edge primitives for the next unicellular proof.

The separately named `SatisfiesReductionRecursion` adds one leading-east
first-bounce clause to the unchanged manuscript-facing `SatisfiesRecursion`.
Its coloring witness, `SatisfiesReductionRecursion.thirdBounce`, and
`SatisfiesReductionRecursion.map` are checked. The generic third bounce uses
explicit q−1 cancellation and constructs both valid successors. The map theorem
transports identities without assuming preservation of cancellation.
No generalized-bounce value theorem, uniqueness theorem, orientation recurrence
bundle, or full semantic bridge is claimed complete.

Recent pushed checkpoints:

- `4d57097`: generic product and north-predecessor reductions.
- `73e8183`: orientation/HRV model and terminating bounce trace.
- `5a33ef9`: uniform orientation column formula and coloring bridge.
- `5a3b763`: reviewed sufficient-certificate proof route, recorded before implementation.
- `4d136c7`: orientation multiplicativity and generic single ND reduction.

Current source batch: full/default build (1446 jobs), all 212 public axiom
checks, global source/line-length guards, immutable-reference/initial-commit
checks, and external-cache checks pass. Only standard Lean axioms occur.
Logs are under `/lake-cache/ai-projects/build/VerticalStripLLT/`:

- `orientation-product-full-build.log`
- `orientation-product-axioms.log`

## Live work and next action

Issues #1–5 are complete. Issue #6 tracks the orientation initial, product,
and unicellular identities; its column and product criteria are complete:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/6.

Aristotle project `17bb2b30-57ab-40bf-b054-9640ec896ffc`, task
`188a6fed-48fe-4246-99e8-26055f8683ba`, is confirmed `IN_PROGRESS` on
`orientationExpansionAt_unicellular`. Observe this same job; do not restart
because an observer expires. Its checked input has sixteen modules and the
fresh-edge helpers. Provenance and request directories are in `docs/ARISTOTLE.md`.

The previous multiplicativity job `1d37e685-a581-4682-9b48-08fdcd5f3be6`,
task `d1be4127-7c06-4481-b02c-2da410c82198`, completed and is integrated.
Its supplied modules were byte-for-byte unchanged. Luna ported three modules;
primary repaired namespace and two `ReflTransGen.lift` API details.

Next: port/check the unicellular result, then prove the direct orientation
bounce identities. In parallel, turn the checked prefix trace into valid
generalized-bounce transformations and lexicographic uniqueness under the
separately proved sufficient certificate. Preserve shifted positivity and
degree/stability as further requirements of the full objective.

## Ownership and build discipline

Primary `/root` owns strategy, integration, all source files, and the sole
project build slot. All Luna/Terra implementation tasks are returned and
released. New build-free assignment: `path_invariants` owns only
`SecondBounceGeneral.lean`. `column_paths` owns only `BounceCoordinates.lean`,
converting east-free prefix counts to the endpoint certificates.
The unrestricted coloring DN candidate has returned to primary.
New build-free assignment: `path_invariants` owns `ReductionRecursion.lean`,
`ReductionRecursionMap.lean`, and `ColoringReductionRecursion.lean` to add and
transport the explicitly required second leading-east clause. No local Lean build or nested Claude process is active.
`bounce_audit` has a read-only follow-up audit of the generalized-bounce trace
interface; it owns no file. No other worker owns an active edit.

Keep local builds serialized globally. Inspect Lean/Lake processes before
each invocation; use `lake-workspace` with reduced priority, never plain Lake.
Luna remains the default build-free implementation worker. Record disjoint
ownership before new tasks. User-authorized Terra/Claude audits and Aristotle
proof searches may run in parallel; primary alone checks and pushes source.

## Source obligations and decisions

`docs/FORMALIZATION.md` is the source map. `docs/RECURSION_PLAN.md` records
measures and the checked product/north branches. `docs/BOUNCE_TRACE_PLAN.md`
records the strict-gap prefix trace. `docs/ORIENTATION_MODEL.md` records the
independent finite orientation/HRV expression.

`docs/REDUCTION_CERTIFICATE.md` records the reviewed route to the unconditional
main expansion through identities proved directly for both semantic models.
Do not rename its stronger predicate to `SatisfiesRecursion`, assume its
orientation witness, or claim original restricted uniqueness is proved.

The generic restricted-east-middle search terminated `COMPLETE_WITH_ERRORS`
(project `09862def-0239-41ee-a563-b12536df8d1f`). Its target remains unproved.
A separate size-at-most-four nonderivability candidate is archived externally
and audited read-only by Terra, but not locally verified or imported. It does
not refute the full recurrence or the manuscript's elementary specialization.
See `docs/RESTRICTED_BOUNCE_AUDIT.md`. No external blocker applies.

## Environment

Initialization commits `830cc6b`, `130f7e8` and reviewed architecture `81b4885`
are preserved. Reference files are unchanged from `130f7e8`; never edit them.
Lean is `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected; never run `lake update`.
No local `.lake/packages` or `.lake/build` exists. Use invocation-local HTTPS
rewriting plus `gh auth git-credential` to push; configured remotes stay unchanged.

Aristotle uses isolated Lean/Mathlib 4.28 snapshots; local 4.34 checks are
authoritative. Only one remote project has been accepted concurrently. Never
infer submission success solely from CLI exit zero; require project/task IDs.
All generated requests, archives, and audit candidates stay outside the checkout.
Previous goal turns and this continuation made verified proof progress; the
full objective remains active. Older inventories are under `docs/archive/`.

New source audit in progress: the DD induction at manuscript LLTe_1 uses a DN
instance with middle eV'', so the current NN-only additional field does not
yet justify the generalized-bounce step. Terra is checking the exact need for
a second leading-east clause; both concrete semantic proofs support the
unrestricted DN statement. The already checked generic single ND theorem
remains valid with its current hypotheses.

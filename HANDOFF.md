# VerticalStripLLT handoff

## Current state

The ordinary LLT expansion remains the active goal; it is not yet proved.
The first three recursion clauses are checked uniformly in all finite
alphabets: `coloringLLT_column`, `coloringLLT_concat`, and
`coloringLLT_unicellular`. Both `coloringLLT_firstBounce` and
`coloringLLT_secondBounce` are checked. `coloringLLT_satisfiesRecursion`
bundles these with empty normalization in the faithful named predicate
`SatisfiesRecursion`; it defines no recursive invariant.

The finite path/graph/coloring model is independent of any recurrence.
`EExpansion` and `evalElementary` interpret formal elementary expressions
separately. No general symmetric-functions library or circular work is needed.

Latest source checkpoints, all pushed on private `main`:

- `f7bb5b4`: general unicellular identity and color-swap primitives.
- `b92dbb5`: restricted swap sum, prefix scanners, valid local path swaps.
- `36cc80a`: second-bounce successor and audited coloring-involution plans.
- `c795bc4`: first-bounce identity, modular graph/weight proofs, recursion helpers.
- `91bee5f`: converse column classification and first-east height API.
- `275fb72`: second bounce and the coloring recurrence bundle; issue #4 closed.

Full/default build (1421 jobs), all 140 public axiom checks, source guards,
line-length checks, `git diff --check`, and immutable-reference checks pass.
Only standard Lean axioms occur. Logs:

- `/lake-cache/ai-projects/build/VerticalStripLLT/recursion-support-full-build.log`
- `/lake-cache/ai-projects/build/VerticalStripLLT/recursion-support-axioms.log`

## Live work and next action

Issue #4 is closed with both single-bounce coloring identities proved:
https://github.com/PerAlexandersson/VerticalStripLLT/issues/4.
Issues #1–4 are completed. Read `docs/BOUNCE_PLAN.md` before implementing the
bounce geometry; it records independently audited word/endpoint hypotheses
and the direct coloring involutions, including equality boundary cases.

Both Aristotle single-bounce candidates are complete, ported by Luna,
independently audited by Terra, and locally verified by primary. Issue #4
was closed after checkpoint `275fb72`.
Third-bounce project `13d18bc3-ffad-4cb1-9807-9b4d3cb4cb04`, task
`372dfa89-c025-4779-8611-1fad2f31a341`, is confirmed `COMPLETE` (100 percent).
Downloaded `third-bounce/completed-candidate.lean` is awaiting local port.
It must construct both valid successor paths and prove the third coloring
identity for every finite alphabet, with no assumed graph identities.
All remote provenance, inputs, outputs, and environment details are in
`docs/ARISTOTLE.md`. Observe this same task; do not restart it on an observer
expiration.

Claude Sonnet completed the read-only recursion audit (native exec session
`56969` exited successfully). Primary checked its claims against the manuscript;
see `docs/RECURSION_PLAN.md` for accepted conclusions and corrections.
Prompt/output: `/lake-cache/ai-projects/requests/VerticalStripLLT/recursion-audit/`.
No nested Claude process remains active.

Next: locally verify the returned third-bounce candidate. The north/east
reduction, diagonal-return split, positive-path east-step lemma, and recurrence
transport are all checked; declaration details are in `RECURSION_PLAN.md`.
`RESTRICTED_BOUNCE_AUDIT.md` records a newly identified generic proof
obligation: the displayed third-bounce derivation invokes a first-bounce
instance with middle eV, outside the restricted recurrence. This is not a
counterexample or a reason to change the target. Claude Sonnet completed its independent read-only audit (session `63513`,
exit 0). Primary accepted the local-diagram finding but rejected unsupported
claims of global nonimplication and the speculative extra-bounce route; see
`RESTRICTED_BOUNCE_AUDIT.md`. No nested Claude process remains active.
Prompt/output are under external `restricted-bounce-audit/`.

## Ownership and build discipline

Primary `/root` owns strategy, integration, and the sole project build slot.
The first-bounce Luna port assignments are complete; primary owns:
`BounceScanners.lean`, `FirstBounceGraph.lean`, `BounceWeight.lean`,
`FirstBounce.lean`, `WordCounts.lean`, and `PolynomialCancellation.lean`.
The full build and axiom checkpoint passed; no local build is active.
Terra independently audited the completed first-bounce candidate and confirmed
source fidelity, unchanged definitions, and derived graph hypotheses.

`ColumnCharacterization.lean` and `FirstEast.lean` are now primary-owned,
locally verified, and included in the full/default build and axiom audit.
Exact public declarations: `Step.valid_one_east_column`,
`Step.valid_one_east_column_size`, `Step.firstEastHeightFrom_append_east`,
`Step.exists_east_decomposition`, `Step.firstEastHeight_eq_counts`, and
`Step.firstEastHeight_append_east`. No subagent owns an active edit.

Second-bounce scanner/graph ports are complete and primary-owned;
`column_paths` returned `SecondBounceWeight.lean` and `SecondBounce.lean`;
primary now owns them. `Recursion.lean` and `ColoringRecursion.lean` have been returned and are
primary-owned for verification: the normalized recurrence predicate and its
coloring-semantic witness. No recursive invariant is defined.
Terra `bounce_audit` independently audits the candidate read-only.
Primary owns integration, docs, source guards, and the sole local build slot.

`NorthEastReduction.lean` and `PathSplit.lean` have passed focused builds;
primary adopted them and is completing the full checkpoint. No active edits
remain on those files. `NonemptyPath.lean` and `RecursionMap.lean` have also been returned and are
primary-owned for final verification. No subagent currently owns an edit.

All three third-bounce port files have been returned to primary:
`ThirdBouncePath.lean`, `ThirdBounceWeight.lean`, and `ThirdBounce.lean`.
Primary is checking imports and local syntax before their batch build.
Terra audits the unchanged target and unrestricted helper read-only.
No subagent currently owns an edit.

The user explicitly requests modular code, sparse/batched compilation, and
parallel bounded delegation to Aristotle and smaller Claude/Luna/Terra models.
Primary still performs the authoritative local builds. Check no global Lean/
Lake process is active before each invocation; use only `lake-workspace`,
reduced priority, and an appropriate compiler timeout. Never use plain Lake,
edit generated cache files, or change dependencies to fit a remote candidate.

## Checked supporting modules

`ColumnBase.lean` proves the general initial condition. `ColoringConcat.lean`
proves graph decomposition, weight factorization, and coloring multiplicativity.
`Unicellular.lean` proves marked-edge scanner/finset identities and the general
unicellular polynomial relation.

`ColoringSwap.lean` gives the swap involution and monomial preservation.
`SwapSum.lean` proves admissibility/ascent/weight and restricted-sum statements
under explicit graph symmetry hypotheses. `FirstBounceGraph.lean` proves those graph hypotheses for the first bounce;
`FirstBounce.lean` gives the resulting full path-based coloring identity.

`PrefixScanners.lean` gives unconditional arbitrary-prefix append laws.
`BouncePath.lean` proves the two valid local swaps; `SecondBouncePath.lean`
composes them into the second successor. These helpers are not bounce identities.
The source map is in `docs/FORMALIZATION.md`; earlier declaration inventories
and checkpoint history are in `docs/archive/handoff-through-bounce-helpers.md`.

## Environment and remaining theorem work

Initialization commits `830cc6b`, `130f7e8` and reviewed architecture `81b4885`
are preserved. Reference files remain unchanged from `130f7e8`.
Lean is `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The wrapper package-directory warning is expected; never run `lake update`.
No local `.lake/packages` or `.lake/build` exists. Dependencies/builds live
under `/lake-cache/ai-projects`.

SSH push authentication is unavailable. Use invocation-local HTTPS rewriting
and `gh auth git-credential`, preserving the configured remote. Lean MCP defaults
to RealRooted: use explicit-root read-only searches and local wrapper checks.
Aristotle uses an isolated Lean/Mathlib 4.28 snapshot; local 4.34 verification
is authoritative. No local toolchain or account changes are permitted.

After single-bounce proofs: generalized bounce reduction; decrease lemmas for
`(size, east count, first-east height)`; recurrence uniqueness; recursive
invariant with named coloring bridge; independent orientation/HRV expression
and its recurrence; ordinary expansion, shifted positivity, degree/stability.
The manuscript's `F_ne=1` typo is resolved as `e₁`. Cancellation of q−1 over
integral coefficient rings must be justified explicitly.

Current checkpoint after `275fb72`: checked north/east reduction, diagonal
return split, positive-path east-step existence, and recurrence transport.
Primary is verifying the third-bounce port next. Aristotle's third job and
the nested Claude audit both completed; no new remote proof has been submitted.
Previous goal turn was verified progress; this continuation has further
checked proof progress. No blocker applies.

# VerticalStripLLT handoff

## Active continuation: deeper interior circular ND

The full circular coloring–HRV equality remains open. The checked outer
induction has one explicit input, `InteriorNDInductionStep`. First-contact
interior overlap is proved; deeper contacts remain. Follow the author's
one-bounce elimination strategy. Strict cycles make both actual models vanish;
overlap between offset contact tracks alone is not a cycle. No flip work.

Author clarification rechecked against the ordinary proof: multiple contacts
are eliminated by paired ordinary/raised child equations and cancellation.
`SatisfiesReductionRecursion.generalizedThirdBounce_word` in
`GeneralizedThirdBounce.lean` uses a shorter-prefix induction for the raised
child, not smaller area. The circular task is to complete that child-equation
assembly after the checked one-bounce restart. Do not require termination of
every arbitrary DD/DN/R1 rewrite sequence. Primary and independent Astra audit
agree; see the ordinary-proof mapping in `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.
That clarification was recorded at `6ae30bd` without a build.

## Current verified checkpoint: exact interior restart type

`DDLocalData.resolved_strictAt_interior` proves that the restart terminal is
strict for every index i≥2. Together with `InteriorRestart`,
`DDLocalData.exists_oneBounceDNData_of_interior_overlap` constructs actual
DN successor data. First-contact NN is already solved; all deeper restarts
are DN, so their neutral move still requires the subsequent child assembly.
Terra supplied the bounded build-free candidate; primary corrected inequality
arguments and constructor application, then verified it. Full build 1881 jobs;
axiom inventory 1857 declarations, standard axioms only. Logs:
`interior-dn-restart-build.log`, `interior-dn-restart-full-build.log`, and
`interior-dn-restart-axioms.log` under the external request directory.

## Shortened-root cycle checkpoint: `eb62e69`

`Diagram.shortenEligible_not_admissible_of_interior_overlap` now proves that
shortening the original eligible root of any acyclic interior-overlap source
creates a strict cycle. The two corollaries
`coloringLLT_shortenEligible_eq_zero_of_interior_overlap` and
`shiftedOrientationExpansion_shortenEligible_eq_zero_of_interior_overlap`
prove vanishing of the actual models at that target. The stronger statement
needs neither saturation nor terminal strictness hypotheses. No source
recurrence or full interior equality is claimed.

Primary implemented the path transport after Luna returned build-free API
notes. Independent Astra review approved the statement and proof. Focused and
full builds passed (1880 full jobs); the complete axiom inventory checked
1855 declarations against the standard-axiom whitelist. Source guards,
100-column limit and diff whitespace passed. Logs are
`interior-shorten-cycle-build.log`, `interior-shorten-cycle-full-build.log`,
and `interior-shorten-cycle-axioms.log` in the external request directory.

The next mathematical task remains matching the restarted raised-child
equations with deleted-child equations into actual corner triples. The new
lemma supplies a checked zero term for the original shortened root.

## Previous semantic checkpoint: `5266faa`

`ChainSingletonData.coloringLLT_shifted_eq_expansion` now proves the actual
coloring–HRV equality for every strict chain plus one isolated vertex and every
finite alphabet, including the empty alphabet. It has no bounce, recurrence,
no-wrap or extra acyclicity hypothesis. The chain length parameter k includes 0.
Both polynomial models retain their independent definitions.

Six modules separate the proof:

- `ChainSingletonSelection`: the finite outgoing/incoming selection sum.
- `ChainSingletonSubsets`: generic removal of forced/cyclic selected edges.
- `ChainSingletonInsertion`: insertion monotonicity, unique occupied gap and
  `xQShift_coloringLLT_closed` for actual coloring.
- `ChainSingletonOrientations`: actual external-selection acyclicity and HRV
  classification, including the winding-sensitive early-out potential argument.
- `ChainSingletonReduction`: internal normal-edge factors and index reindexing.
- `ChainSingletonExpansion`: the final actual-model equality.

The resulting common expression is
(1+q)^A * (e_1*e_(k+1) + r*q*e_(k+2)), where A=I+M,
I counts forward internal normals, M counts outgoing positions before the last,
and r=M+[incoming at first]+[outgoing at last]. The formula is uniform in k,m.

Checks: full default build 1879 jobs; axiom inventory 1852 declarations, only
propext, Classical.choice, Quot.sound. Source guards, line lengths and diff
whitespace pass. External logs `chain-singleton-checkpoint-build.log` and
`chain-singleton-checkpoint-axioms.log` under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`. Builds were globally serialized.

## Ownership

Primary owns strategy, integration, remote jobs, all other source and the sole
build slot. All delegated lanes are released. Luna ported selection/subset sums;
Terra extracted insertion/coloring proofs; primary ported HRV and assembly,
repaired Lean4.34 APIs, eliminated a slow congruence step, and verified everything.
Astra independently audited actual semantics, winding, boundary cases and the
unchanged final statement. No build-slot transfer occurred.

Use only `lake-workspace`; check no other Lean/Lake process is active before
every invocation. No delegate source edits remain pending.

## Aristotle provenance

The renewed full interior request is IN_PROGRESS in the existing project
`65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, new task
`a430cbfd-eb82-4070-b9c2-002ae875cb53`. Original observer **55772** lost its
connection; task status remained IN_PROGRESS. Replacement native observer
session **39014** also lost its connection. Task status remained IN_PROGRESS;
replacement session **59744** writes
`circular-interior-with-chain-base/observer-reconnected-2.log`. Observe this exact task;
reconnect after transient observation failures without resubmitting it. This
observer does not download: after completion explicitly download the project
archive into `circular-interior-with-chain-base/result.tar.gz`.

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

## Remaining mathematics and next step

Prove a general exit for deeper interior contacts, then discharge
`InteriorNDInductionStep` and transfer the already-proved HRV positivity/degree.
The DD-resolved child has doubled area D+1. Its checked one-bounce restart is
DN at every deeper contact and preserves that auxiliary area. Mixed DD/neutral termination alone
neither supplies an exit nor covers R1 strictification. Two exposed corners
provide a checked smaller-area exit; a single corner can return to area D
without decreasing strict rank. Rotation alone preserves the scaled semantic
defect and gives no cancellation.

The completed chain-singleton base is useful but does not cover every source:
the saturated acyclic n=8 diagram with areas (3,4,4,4,3,4,5,5) has deeper contact
i=2, one six-vertex strict chain and two isolated vertices. Details are in
`docs/proofs/CIRCULAR_ND_ASSEMBLY.md`. Do not infer a general exit from this base.
Changing its area(0) to 4 preserves that overlap and yields strict component
sizes 6 and 2, with no isolated source vertices. The stronger one-nontrivial-chain
classification is therefore also false (independent hand audit, no new builds).
The active proof-search request uses the newly verified semantic base while
retaining the full interior target and this counterexample to classification.

Checkpoint `5619f82` proves zero-cut confinement and exact zero-row preservation
under concrete DD/DN moves. These moves cannot create an ordinary cut from a
positive-area source. No word decoder or ordinary semantic transport was started.
Checkpoint `fccd19a` records the saturated-source counterexample. Earlier
sources: `78c07c3` separated ND, `8c8e8b5` outer induction, `372619c` corner adjacency.

The ordinary expansion is fully proved. Initialization commits `830cc6b`,
`130f7e8` and immutable `references/alexandersson-sulzgruber-2022/` are preserved.
No Overleaf edits in this continuation. Exact checked interfaces are in
`docs/CIRCULAR_STATUS.md`; remaining obligations in `docs/CIRCULAR_GOALS.md`.
History remains in Git and `docs/archive/`.

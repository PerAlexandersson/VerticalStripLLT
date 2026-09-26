# VerticalStripLLT handoff

## Active continuation: full circular expansion

The full circular coloring–HRV equality remains open. Follow the author's
one-bounce elimination strategy. A contact-track overlap alone is not a strict
cycle; genuine directed strict cycles make both actual expressions vanish.
No flip-component work or new examples in this increment.

Latest pushed source checkpoint: `8c8e8b5` (conditional outer induction), following
`eb11c69` (alphabet stability/two-corner exit),
`f33cdc6` (full DN handoff), `0fc4d07`, `3c7f3d4`
(comparable-edge base) and `1d5005d` (direct ND/full NN).

Current verified increment: complete conditional outer induction, with
`Diagram.expansion_of_nd_induction_step` and
`Diagram.expansion_of_remaining_nd_cases`. The latter has precisely two open
inputs, `SeparatedNDInductionStep` and `InteriorNDInductionStep`. All other
branches are discharged internally using the actual models. Independent Astra
review confirmed exhaustive cases, valid measure decreases and exact agreement
with the two remote targets. This does not prove either remaining input.

Previous verified increment: direct alphabet stability and the two-corner
auxiliary exit. Exact new interfaces are `EdgeData.specializeLast_coloringLLT`,
`Diagram.specializeLast_coloringLLT`,
`Diagram.expansion_of_two_nonstrict_corners`, and
`DDLocalData.expansion_of_resolved_two_corners`. The alphabet theorem follows
from the coloring sum without the unfinished circular bridge. The two-corner
exit uses two actual R1 identities; its geometric hypothesis still needs to be
established where this exit is used in the remaining overlap argument.

Previous verified increment: full DN elimination, with exact declarations
`Diagram.exists_dn_reduction` and `Diagram.expansion_of_dn`. The actual
successor preserves doubled half-square area, decreases strict rank, remains
strictly acyclic and preserves both independently defined polynomial models.
`IsDNTarget` describes actual rows; it is not a recurrence-defined invariant.
Both DD children are handled by contact-count induction and a concrete closing
triple, never by outer area induction at a larger diagram.

Already complete: full NN (`expansion_of_nn`), direct ND
(`expansion_of_oneBounce_nd`, area drops two/four), root-alias ND, strict-cycle
vanishing, and the normal-comparability semantic base. Exact source links and
all previous completed interfaces are in `docs/CIRCULAR_STATUS.md`.

Checks: full default build 1857 jobs; axiom inventory 1589 declarations, only
propext, Classical.choice, Quot.sound. Source guards, line lengths and relative
documentation links pass. Reference files remain unchanged. External logs:
`circular-induction-checkpoint-build.log`,
`circular-induction-checkpoint-axioms.log`. Earlier alphabet/DN/NN/ND and comparable-base logs
are retained. Initialization commits `830cc6b` and `130f7e8` remain intact.

## Ownership and active work

Primary owns strategy, integration, source, remote jobs and the sole globally
serialized local build slot. Use only `lake-workspace`; check for other Lean
builds before every invocation. No build-slot transfer has occurred.

Terra supplied `ColoringAlphabet` and Luna supplied `DoubleCornerReduction`.
Primary repaired and verified these, added the generic finite-sum argument and
Diagram wrapper in `AlphabetStability`, and added the DD two-corner wrapper.
All delegated edit lanes are released. Primary owns all source and checks.
All delegates remain build-free.
Luna's outer-induction lane returned without edits. Primary implemented and
verified `ExpansionInduction` and `NDInductionCases`; Astra independently
reviewed them. All delegated edit/review lanes are released. No recurrence-defined
polynomial is introduced.
Astra's read-only draft audit found no additional primitive circular base or
root-selection condition; the intended local elimination still needs explicit
interior exit accounting. Active Aristotle separated-ND project
`361812e0-b73e-48b9-9ad7-dffe103615f6`,
task `e58bd214-3a7c-4d47-ab01-e58521c293ad`. Native observer session 45949;
request/result directory `circular-separated-nd/` under the external requests
cache. Source commit `0fc4d07`; 175 modules, exact target and hashes retained.
Observe this same task and integrate only appended proof modules after review.
The CLI can exit zero on API errors, so inspect logs as well as exit status.

Aristotle full DN project `ae819e79-2742-4965-9254-8eef5929cfa0`, task
`0216c708-f9a4-4baa-82d0-d98d33d8e293`, is complete and locally integrated in
`DNReductionTarget`, `DNReductionDiamond`, `DNReduction`, and the primary's
`FullDNRecurrences`. Shared shift-injectivity declarations moved unchanged to
`QShiftInjective`; no duplicated service prefix was imported. Independent
Astra audit approved mathematical fidelity and unchanged hypotheses.

The interior-overlap request is fully prepared in `circular-interior-expansion/`.
It now includes the checked `DoubleCornerReduction` module from `eb11c69`
(176 modules), with unchanged target and updated hashes/proof-route notes.
A concurrent submission was rejected: "You have too many projects in progress."
No project/task ID was created for it. Submit this saved request after the active
separated-ND task completes; do not cancel other projects to obtain a slot.
Its exact target is `expansion_of_nd_interior_overlap`, with saturated source
and the explicit smaller `(doubledArea, strictRank)` semantic induction hypothesis.
This is the unresolved interior exit argument, not an assumed recurrence. Astra's remaining ND audit,
including rejected shortcuts, is in `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.
Completed direct-ND and full-DN remote provenance is in `docs/ARISTOTLE.md`.

## Next steps and limits

1. Prove separated-contact ND transport/cancellation, including cyclic
   intermediates using strict-path splicing or paired-chain conjugacy.
2. Finish interior-overlap ND elimination/restart assembly. Direct ND, root-alias
   ND, and the uniform interior-overlap restart are already checked.
3. Instantiate the checked outer induction with these two proved inputs, then
   transfer the independent HRV positivity and degree statements to coloring.

`LocalEliminationStep.measure_lt` proves termination of mixed concrete DD/neutral
segments by `(strict.card, strictRank)`. It does not cover R1 strictification
or assert existence of a next move. Resolved DD children have doubled area D+1;
outer induction alone cannot justify their semantic equality. Deleted children
have area D−1. Preserve this distinction in the remaining ND assembly.

Completed results: `docs/CIRCULAR_STATUS.md`. Remaining obligations:
`docs/CIRCULAR_GOALS.md`. Proof explanations are indexed by `docs/README.md`.
Earlier checkpoints: `130efc2` (interior restart/mixed termination), `398006c`
(resolved DD child), `377ae36` (root-alias ND). Older chronology is retained in
`docs/archive/HANDOFF_THROUGH_INTERIOR_RESTART.md`.

Overleaf path drift: `old-main.tex` is absent; `main.tex` holds the former long
draft and `new-main.tex` is present. No Overleaf edits in this continuation.
Author-supplied files under `references/alexandersson-sulzgruber-2022/` remain
immutable.

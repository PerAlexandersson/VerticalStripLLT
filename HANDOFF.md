# VerticalStripLLT handoff

## Active continuation: full circular expansion

The full circular coloring–HRV equality remains open. Follow the author's
one-bounce elimination strategy. A contact-track overlap alone is not a strict
cycle; genuine directed strict cycles make both actual expressions vanish.
No flip-component work or new examples in this increment.

Latest pushed checkpoint: `3c7f3d4` (comparable-edge semantic base), following
`1d5005d` (direct ND and full NN elimination).

Current verified increment: full DN elimination, with exact declarations
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

Checks: full default build 1852 jobs; axiom inventory 1576 declarations, only
propext, Classical.choice, Quot.sound. Source guards, line lengths and relative
documentation links pass. Reference files remain unchanged. External logs:
`circular-full-dn-checkpoint-build.log`,
`circular-full-dn-checkpoint-axioms.log`. Earlier NN/ND and comparable-base logs
are retained. Initialization commits `830cc6b` and `130f7e8` remain intact.

## Ownership and active work

Primary owns strategy, integration, source, remote jobs and the sole globally
serialized local build slot. Use only `lake-workspace`; check for other Lean
builds before every invocation. No build-slot transfer has occurred.

Luna supplied bounded ports and direct NN/DN interfaces; primary repaired and
verified them. All delegated file lanes are released. Primary owns all current
source and checks. No remote proof task is active.

Aristotle full DN project `ae819e79-2742-4965-9254-8eef5929cfa0`, task
`0216c708-f9a4-4baa-82d0-d98d33d8e293`, is complete and locally integrated in
`DNReductionTarget`, `DNReductionDiamond`, `DNReduction`, and the primary's
`FullDNRecurrences`. Shared shift-injectivity declarations moved unchanged to
`QShiftInjective`; no duplicated service prefix was imported. Independent
Astra audit approved mathematical fidelity and unchanged hypotheses.

The interior-overlap request target/proof notes are prepared externally in
`circular-interior-expansion/`, not yet submitted. Astra's remaining ND audit,
including rejected shortcuts, is in `docs/proofs/CIRCULAR_ND_ASSEMBLY.md`.
Completed direct-ND and full-DN remote provenance is in `docs/ARISTOTLE.md`.

## Next steps and limits

1. Prove separated-contact ND transport/cancellation, including cyclic
   intermediates using strict-path splicing or paired-chain conjugacy.
2. Finish interior-overlap ND elimination/restart assembly. Direct ND, root-alias
   ND, and the uniform interior-overlap restart are already checked.
3. Assemble outer half-square-area/strict-rank induction, then transfer the
   independent HRV positivity and degree statements to coloring.

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

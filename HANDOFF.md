# VerticalStripLLT handoff

## Active continuation: full circular expansion

The full circular coloring–HRV equality remains open. Follow the author's
one-bounce elimination strategy. A contact-track overlap alone is not a strict
cycle; genuine directed strict cycles make both actual expressions vanish.
No flip-component work or new examples in this increment.

Latest pushed checkpoint: `1d5005d` (2026-09-26), following `aecea0f`:

- `Diagram.exists_oneBounce_nd_reduction`: direct ND for both independently
  defined models; doubled-area drops two/four, no acyclicity or no-wrap input.
- `Diagram.expansion_of_oneBounce_nd`: both targets supplied by outer area
  induction. Source: `Circular/OneBounceNDRecurrences.lean`.
- `DDLocalData.closingDN_target_eq_deleteCorner`: deletion side of the NN
  closing triple. `coloring_closing_nn` and `orientation_closing_nn` prove
  the actual difference formulas using direct DN and R1.
- `Diagram.shifted_nn_of_counted`: full NN identity for every DD count, by
  induction over actual child searches and cancellation of q.
- `Diagram.expansion_of_nn`: complete NN semantic induction step, final
  doubled-area drop two. Source: `Circular/NNElimination.lean`.

Next verified increment: the complete semantic base
`coloringLLT_shifted_eq_expansion_of_normal_comparable` (including
`coloringLLT_shifted_eq_expansion_of_strict_total`) and
`neutralExchange_acyclic_iff`, which transports cycles under explicit separated
inner paths without assuming acyclicity or distinct outer endpoints.

Checks: full default build 1847 jobs; axiom inventory 1560 declarations, only
propext, Classical.choice, Quot.sound. No placeholders or unchecked native
proofs; source guards, relative documentation links and immutable reference
hashes pass. External request-directory logs:
`circular-comparable-checkpoint-build.log`,
`circular-comparable-checkpoint-axioms.log`; earlier NN/ND logs are retained.
The two initialization commits `830cc6b` and `130f7e8` remain intact.

## Ownership and active work

Primary owns strategy, integration, source, remote jobs and the sole globally
serialized local build slot. Use only `lake-workspace`; check for other Lean
builds before every invocation. No build-slot transfer has occurred.

Luna supplied bounded ND ports and direct NN/DN interfaces. Primary adopted,
repaired and locally verified them. Luna returned `Circular/NeutralExchangeAcyclic.lean`; primary adopted the
proof repairs and verified it locally. Luna returned API notes only for `Circular/ComparableExpansion.lean`; primary
owns its implementation and local checks. All delegated lanes are released.
Astra completed a read-only audit of the remaining longer-search ND assembly;
its precise obligations and rejected shortcuts are recorded in
`docs/proofs/CIRCULAR_ND_ASSEMBLY.md`. Terra has no active assignment.

Completed direct-ND Aristotle project `7f814d1b-422f-469b-b0f8-cc2696e9518e`,
task `bc03be2f-39de-4689-ba9b-4ab97ef9bb9c`, is locally integrated. Only appended
proof modules were ported; existing mathematical definitions stayed unchanged.
Independent Astra review checked the final hypotheses, seven relations and
shift injectivity. Remote provenance: `docs/ARISTOTLE.md`.

Sole active remote task: full DN elimination, project
`ae819e79-2742-4965-9254-8eef5929cfa0`, task
`0216c708-f9a4-4baa-82d0-d98d33d8e293`. Request, source hashes and native observer
log are under `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-full-dn/`.
Native observer session 48054 downloads `result.tar.gz` on completion. Observe
this task; do not resubmit if the observer disconnects. Exact target
`Diagram.exists_dn_reduction`: actual coloring/HRV identities, same half-square
area, preserved strict acyclicity and decreased strict rank. It requests local
DD elimination and a concrete DN closing triple, not projected ND/R4.

## Next steps and limits

1. Integrate the actual full DN reduction after independent review and local
   serialized checking; its geometry and termination are already proved.
2. Finish longer-search ND elimination/restart assembly. Direct ND, root-alias
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

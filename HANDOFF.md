# VerticalStripLLT handoff

## Active continuation: full circular expansion

The full circular coloring–HRV equality remains open. Follow the author's
one-bounce elimination strategy; an overlapping contact track alone is not a
strict cycle. Genuine strict cycles make both actual expressions vanish.
No flip-component work or new examples in this increment.

Current verified increment (2026-09-26): interior ND overlap restarts at an
eligible zero-DD NN/DN contact after DD resolution. Exact theorem:
`DDLocalData.exists_oneBounce_restart_of_interior_overlap` in
`Circular/InteriorRestart.lean`. No no-wrap or new recurrence hypothesis.

Latest pushed checkpoint: `130efc2`, interior restart and mixed DD/neutral
termination, after `398006c` (resolved DD child). This checkpoint also verifies:
- `DDLocalData.resolved_doubledArea`: resolved child gains one half-square;
  `deleted_doubledArea`: deletion child loses one half-square.
- `DDLocalData.expansion_of_children`, `expansion_of_resolved`: assembly from
  actual independent identities; the larger child's equality remains an
  explicit input, never an unjustified outer induction hypothesis.
- `Diagram.exists_ndLocalData`: uniform direct ND geometry, no acyclicity
  assumption; `NDLocalData.shortened_doubledArea` drops two half-squares.
- `Diagram.lowerStrict_strictAt_iff`, `lowerStrict_boundary`: exact head-left
  row transport.

Checks: full default build 1835 jobs; axiom inventory 1378 declarations, only
propext, Classical.choice, Quot.sound. Logs in the external request directory:
`circular-closing-checkpoint-build.log` and
`circular-closing-checkpoint-axioms.log`. Immutable references unchanged.

## Ownership and active work

Primary owns strategy, integration, remote jobs, all unassigned source, and the
sole globally serialized local build slot. Use only `lake-workspace`, with a
process check before every invocation. No build-slot transfer has occurred.
Luna returned `Circular/LocalEliminationTermination.lean`; primary adopted its
repairs and corollaries. Luna returned `Circular/DiagramExt.lean`; primary adopted its dependent-type
repairs. Luna returned `Circular/ShortenStrictRows.lean`; primary adopted its repairs.
Luna returned `Circular/EligibleCornerMoves.lean`; primary adopted its repairs.
All delegated file lanes are released.
Primary owns new `Circular/EligibleShorten.lean` and
`Circular/DDClosingNN.lean` for the concrete NN closing triple. The raised-side
identity `DDLocalData.resolved_shorten_eq_unstrict` passes its focused build;
remaining closing identity is the deletion side. `DiagramExt` and root-shortening
row interfaces and eligible-root preservation pass the full root and axiom checks.
Astra reviewer is read-only; its direct ND and auxiliary termination audits
are complete. Terra returned no candidate and has no active assignment.

Aristotle sole active remote job: direct one-bounce ND, project
`7f814d1b-422f-469b-b0f8-cc2696e9518e`, task
`bc03be2f-39de-4689-ba9b-4ab97ef9bb9c`. Request and native observer:
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-direct-nd/`.
Exact target `Diagram.exists_oneBounce_nd_reduction` gives valid targets,
doubled-area drops two/four, actual coloring coefficients q−1/q, and actual
shifted HRV coefficients q/q+1. No acyclicity or no-wrap assumption.
Observe the same task; do not resubmit because an observer disconnects.

Restart project `6654bca9-3649-4ebd-b9b8-ae1cc3050caa`, task
`0f992037-5575-4c13-bd41-75c4694b8651`, is complete and locally integrated.
Luna ported only its final theorem; current checked prefix stayed intact.

## Next steps and limits

Mixed DD/neutral termination is now locally proved using lexicographic
`(strict.card, strictRank)`. Exact declarations in `LocalEliminationTermination`:
`LocalEliminationStep.measure_lt`, `strict_cycle_of_infinite_local_elimination`,
and vanishing of both actual polynomial expressions. This covers those moves
only, not R1 strictification or existence of a next move. Integrate the direct ND
identity, complete local elimination/cancellation, and assemble the outer
half-square-area induction. The root-alias branch is already complete through
`Diagram.expansion_of_nd_alias` (`377ae36`). Counts/contact lists are auxiliary
bookkeeping; a projected general multi-bounce R4 identity is not required.

See `docs/CIRCULAR_STATUS.md` for verified interfaces,
`docs/CIRCULAR_GOALS.md` for remaining work, and `docs/ARISTOTLE.md` for remote
provenance. The exact direct-ND seven-relation plan is in
`docs/proofs/CIRCULAR_DIRECT_ND.md`. The corrected overlap analysis and existing
Rust cross-checks are in `docs/proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md`.

Overleaf path drift: `old-main.tex` is absent; `main.tex` holds the former long
draft and `new-main.tex` is present. No Overleaf edits in this continuation.
Author-supplied references remain immutable. Initialization commits `830cc6b`
and `130f7e8` are preserved. Completed chronology:
[archive](docs/archive/HANDOFF_THROUGH_INTERIOR_RESTART.md).

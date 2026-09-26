# VerticalStripLLT handoff

## Completed: full aggregate circular HRV formula

The ordinary and aggregate circular LLT expansions are proved. The circular
formula holds for every manuscript circular Dyck/Motzkin diagram and every
finite alphabet, including the empty alphabet. No recurrence, acyclicity,
saturation or no-wrap hypothesis remains in the final theorem.

Public declarations in `VerticalStripLLT/Circular/Expansion.lean`, namespace
`VerticalStripLLT.Circular`:

- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`;
- `coloringLLT_shifted_eq_orientation_sum`;
- `coloringLLT_shifted_e_positive` (one expression for all alphabets,
  nonnegative q-coefficients, weighted degree n).

The coloring sum and integer-cover HRV expression are independently defined.
See `docs/CIRCULAR_COMPLETION.md` for the source correspondence and scope audit.
The flip-component identity remains unproved; aggregate positivity does not
establish component positivity. The user explicitly notes that a complete
component proof may not yet be known. No component proof is assumed here.

## Final checked increment

Verified theorem checkpoint: `18fbb4d` on private `main`.

The previous pushed checkpoint is `5f6cd6f` (actual residual coloring and HRV
transport). This completion adds four modules:

- `ComponentFactorization`: strict-chain comparability partitions internal
  normal edges; both actual models have the same forced factor within each
  diagram. `expansion_iff_component_residual` cancels its nonzero scalar.
- `InteriorComponentPaths`: source and actual reversal-target strict
  comparability, derived from the concrete component geometry.
- `InteriorReversalReduction`: `expansion_of_reversalTarget`,
  `Diagram.expansion_of_nd_interior_overlap` and `interiorNDInductionStep`
  discharge the unchanged interior induction interface using a strictly
  smaller doubled-area target.
- `Circular.Expansion`: unconditional aggregate equality and positivity.

Independent Astra review approved source fidelity, scope, actual residual
semantics, all-alphabet cancellation and the final induction hypotheses.
Luna supplied component-path candidates and documentation cleanup; Terra
reviewed scalar APIs. Primary corrected, integrated and verified the code.

Verification passed with Lean 4.34 and the pinned Mathlib manifest:

- Focused `Circular.Expansion` build: 1772 jobs.
- Full default `lake-workspace build`: 1908 jobs.
- `lake-workspace env lean Verification.lean`: all 2037 inventory declarations
  present in exact order; only `propext`, `Classical.choice`, `Quot.sound`.
- No proof placeholders, custom axioms, native unchecked proofs or unsafe
  declarations; Lean source width ≤100; `git diff --check` passes.
- Initialization commits `830cc6b`, `130f7e8` remain ancestors; immutable
  `references/alexandersson-sulzgruber-2022/` unchanged from initialization.

External logs under `/lake-cache/ai-projects/requests/VerticalStripLLT/`:
`circular-expansion-build.log`, `circular-expansion-full-build.log`,
`circular-expansion-axioms.log`. The final four modules were compiled after
formatting changes in the full build. No dependency update or local generated
build directory was introduced.

## Ownership and next step

Primary owns strategy, final integration, this handoff and the sole local
build slot. All delegate edit lanes, including Luna's documentation cleanup, are released.
No build-slot transfer occurred. No local build or remote proof request is active.
Use only `lake-workspace`; check for other Lean/Lake processes before every
invocation. Lean MCP targets RealRooted and is not used for implicit checks.

There are no remaining proof obligations for the aggregate circular goal.
The next research stage is an audit of the full flip-component identity in
`docs/CIRCULAR_FLIPS.md`: distinguish proved foundations from conjectural
component steps before implementation. The strict/weak omega translation is
separate. Updating the older manuscript proof outline to the verified route
is a writing task; no Overleaf changes were made in this checkpoint.

Historical ownership and geometric checkpoints remain in Git and
`docs/archive/circular-interior-checkpoints-through-e2f3479.md`. Superseded
ND proof-search notes are explicitly marked historical; their unused auxiliary
claims are not asserted to have been proved by the final expansion theorem.

## Aristotle provenance

The existing full interior request finished **COMPLETE_WITH_ERRORS**:
project `65c4cfed-a912-4dc7-9dfc-1901c5f810a7`, task
`a430cbfd-eb82-4070-b9c2-002ae875cb53`. Its final source retains exactly one
placeholder, the full `expansion_of_nd_interior_overlap` target. Nothing from
this return was imported. The only new proved wrapper repeats the existing
first-contact result. Its exploratory rank calculations are not proof of a
mathematical obstruction.

The archive and inspected files are retained externally under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-interior-with-chain-base/`:
`result.tar.gz`, `returned-Request.lean`, `returned-ARISTOTLE_SUMMARY.md`, and
`returned-REMAINING_ISSUE.md`. Final source SHA256:
`680e6d017cb24fe780ec3356e220d4d3bb67670986355a7f693cbbe042b0f2e9`.
Input source was `5266faa`, before the column-reversal construction. No live
remote proof task remains; do not restart an observer for this completed task.

The successful chain-singleton request was already integrated at `5266faa`.
Older request and compatibility provenance is retained in `docs/ARISTOTLE.md`
and the archived handoff. Local Lean4.34 verification remains authoritative.

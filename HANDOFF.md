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

## Active general companion goal

Primary owns strategy and notes. Astra reviewed the sink-deletion proof route;
Terra audited induced circular restriction. Both delegates were read-only and
build-free. The active goal remains unproved.

`docs/proofs/COMPONENT_SINK_BRANCHING.md` records a proved mathematical
reconstruction lemma: restrictions obtained by deleting a fixed sink subset
have constant multiplicity on complete smaller flip components. The remaining
precise companion is (S_k), comparing actual recomputed HRV after deletion
with elementary one-variable branching; the stronger fixed-subset (S_T) is
also proposed. If proved, this gives induction on vertices and alphabet size.
Neither identity is currently proved or formalized. Critical-edge forests
preserve actual lifted HRV, but do not justify discarding coloring constraints.

Aristotle project `d4b3ddfe-0051-4f80-b222-4e9374badcb3`, task
`ae0d9a91-dc02-4f53-97a9-3ed6f8034bcf`, is active. Exact payload, hashes,
submission and steering receipts are external in
`/lake-cache/ai-projects/requests/VerticalStripLLT/component-diamond-companion/`.
The original task `e8ff79a8-7d41-4d95-98ea-34cd691a4653` was cancelled after
an exhaustive n=6/7 enumeration stalled; inline redirection had not changed
the reported computation. The continuation received `SINK_BRANCHING.md`
and explicit proof-only instructions. Its same-task observation wrapper is
running in native session `36244`, with a two-hour allowance and logs in that
directory; IN_PROGRESS confirmed. See the ledger. No result was integrated.

Research checkpoint `8f566ad` is pushed on private main. Whitespace checks
passed; independent Astra and Luna reviews checked the reconstruction/induction
boundary. No source build was appropriate for this documentation checkpoint.

Bounded fixed-subset checks passed for four specified n=4 diagrams, using the
existing Rust HRV API through an external input/output bridge and the prior
finite flip enumerator. These are evidence, not a proof. No shared Rust source,
polynomial family, Lean module, Lean build, or Overleaf edit was introduced.
Primary owns HANDOFF, the new note, docs index and Aristotle ledger.
Luna's external `diamond-exploration/promotion-sweep-probe.py` lane is released.
Primary reviewed, requested specification fixes, and ran the corrected bounded
probe. The descending sweep is REFUTED at n=4. A separate hand-derived n=5
obstruction excludes ANY promotion restricted to root-containing flips; Astra
confirmed it and Rust checked the actual HRVs. Complete-component (S_T) still
passes these examples and all 449 decorated circular n=4 diagrams. The new note
records exact statements; none is mistaken for a proof of (S_T).

The useful surviving ordinary reduction uses the successor-closed set
`{v : HRV(v) <= s}` to reduce an arbitrary sink to a largest-sink promotion.
Such a promotion must allow changes outside the immediate root triangles.
Circular canonical lifts retain period-shift constraints and need an additional
argument. These facts were sent to the active Aristotle task.
`suggestions/flip-enumeration-api.md` records the pending Rust integration task;
no shared Rust ownership or source has been taken over.

## Diamond exploration result

The fixed-diagram diamond-to-chain straightening lemma is REFUTED, not open.
See `docs/proofs/DIAMOND_STRAIGHTENING_AUDIT.md` for a general strict-component
partition obstruction and an exact eight-state separating certificate.
This does not refute the component conjecture.

An auxiliary diamond and an HRV-preserving vertex swap repair the obstruction.
Primary and independent Astra review checked a uniform overlap identity with
arbitrary symmetric exterior. Without symmetry, an explicit exterior-swap
correction remains and cancels for swap-invariant multiplicities. The open
next task is component-labeled packet decomposition, swap balance, and a
justified reduction of the resulting packets. No complete proof is claimed.

In that preceding checkpoint, Astra independently derived the
obstruction and repair; Terra audited the existing HRV triangle APIs. All
read-only delegate lanes were released. No Lean build, new Lean theorem,
remote request or Overleaf edit occurred in that checkpoint.

Rust capability check: read LIBRARY_GUIDE, ran cargo metadata, inspected
LLT/HRV and exact linear algebra APIs. There is no public circular flip/diamond
span API. A bounded one-off Python probe found and exactly checked the span
obstruction; no polynomial family or shared Rust source was introduced.
External artifacts and hashes are in the audit note. Whitespace checks pass.

## Component brainstorming continuation

Completed research note: `docs/proofs/FLIP_COMPONENT_INDUCTION.md`. Astra and
Terra reviewed the current manuscript and component notes read-only; neither
edited or built. Primary wrote and checked the note and index. All delegate
lanes are released. No Lean claims, builds, or Overleaf edits were made.

Key refinement: the recorded target-span obstruction restricts to equal ascent
number; the unweighted component theorem permits cross-ascent target terms.
The first recorded obstruction can use a maximal-ascent target chain singleton
as its signed correction, conditional on the recorded K identity. The uniform
missing steps are simultaneous coloring/HRV transport, global reconstruction
and enough independent equations to isolate each source component.
A follow-up section proposes a shorter common-diamond straightening route.
That fixed-diagram normalization statement is now refuted by the subsequent
audit above. The repaired route allows auxiliary states and certified swaps.

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

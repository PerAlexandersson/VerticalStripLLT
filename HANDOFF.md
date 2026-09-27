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

## Active goal: component HRV formula

The user has redirected the main proof search to the original recurrences,
splitting corners into selected/unselected (strict/deleted) cases. Primary
owns all note edits, including `FLIP_COMPONENT_INDUCTION.md`,
`COMPONENT_ACTIVE_CORNERS.md`, external probes,
the index, Aristotle ledger, and this handoff. Astra audited the two recurrence
repairs and the general always-redundant corner deletion lemma. Luna returned
a read-only API audit; primary corrected two proposed interface pitfalls in
the note. All local delegate lanes are released. The StrongSrc Aristotle task
returned COMPLETE_WITH_ERRORS, without its target proof. A new focused task
on ordinary active-component uniqueness is confirmed IN_PROGRESS in the same project.
No Lean build or Claude process is active.

The full flip-component theorem is unproved. The goal is a general diamond
or companion lemma establishing it, with precise hypotheses and justified
component isolation. Neither finite tests nor the aggregate theorem close it.
The exact target is in `docs/CIRCULAR_FLIPS.md`.

Primary owns strategy, all current notes, integration, and the sole global
Lean build slot. Astra reviewed the new
ambient and compatible-lift reductions; Terra reviewed redundant-edge removal;
Luna returned build-free snippets only. Use only `lake-workspace`, after checking that no
other Lean/Lake build is active. No build-slot transfer has occurred.

The last pushed research checkpoint before this increment is `0135e42`:
compatible-lift reduction to ordinary components. The current recurrence note
is `docs/proofs/FLIP_COMPONENT_INDUCTION.md`; the auxiliary reduction note is
`docs/proofs/COMPONENT_AMBIENT_REDUCTION.md`.
Primary owns it, the source-note/index links, this handoff, and the archive.

## Current proved reductions and remaining obligation

- Forgetting strict decorations identifies ENTIRE components, with the same
  selected relations and semantics; no partial-stratum substitution is used.
- Ambient universality: every component in any circular diagram is an ENTIRE
  component in the unmarked complete circular diagram U_n. A flip cannot leave
  the original diagram, because its retained long edge forces both short edges
  to be natural. Thus the full goal reduces exactly to U_n for all n>=1.
- Removing a projected transitively redundant edge preserves uniform selected
  order enumerators and actual lifted HRV maxima. It does NOT preserve full
  lifted reachability, actual flips, selected-edge count, or multiplicity.
- If all selected edge increments admit compatible integer vertex lifts, each
  flip preserves the SAME lifts. Sorting them identifies the ENTIRE actual
  circular component with an ordinary complete-graph component and preserves
  HRV. Every forest satisfies this condition; in general it is equivalent to
  zero signed winding around every undirected cycle. In such components,
  projected and lifted covers agree. The ordinary component theorem remains
  open, so this is a reduction, not a proof of these component identities.
- Source and sink restrictions with fixed deleted extrema have constant
  multiplicity on complete smaller components. Source deletion also preserves
  the remaining HRV fibers. The source identity (Src), or the sufficient sink
  identity (S_k), would close vertex/alphabet induction; both remain unproved.
- Strong flips require projected cover pairs as well as the actual lifted
  conditions. Their components partition actual components. The same source
  reconstruction works for them, so the new stronger companion (StrongSrc)
  would suffice for the full theorem. Its cancellation remains open.
- Every strong flip on more than three vertices has an exterior source or sink.
  This supplies mixed-deletion coverage, not the missing extension identity.
  General circular flips can fail this condition, and a strong component can
  have a cyclic union of its selected edges. Both obstructions have exact
  four-vertex certificates in the new note.

The next task is uniform component isolation through the manuscript recurrences.
The original two ordinary obstructions now have mathematical coloring-and-HRV
repairs: the first by cancelling solved source components; the second by the
user's corner split at 24 and a product of two diamonds. These exact certificates,
the uniform chain-of-triangles family, and the general always-redundant strict
corner deletion theorem are recorded in `FLIP_COMPONENT_INDUCTION.md`.
The new deletion theorem transports ENTIRE components and lowers doubled area
by one. It handles all three ancillary source components of the first example.
The remaining obligation concerns components where every corner can be a cover
somewhere in the component. The new open ordinary companion (AU) says at most
one such connected component exists at each ascent. Its implication for the
FULL ordinary component theorem is proved: use corner and disconnected-block
reductions, then isolate the sole unknown in the aggregate coefficient.
The exact diagnostic passes all ordinary saturated diagrams through n=6
(196 diagrams, 33,867 states, 4,228 components cumulatively). This is evidence,
not a proof of AU. The direct circular version is false, with a four-vertex
tree counterexample in `COMPONENT_ACTIVE_CORNERS.md`. AU would also settle
balanced circular components; unbalanced components still need an argument.
Aristotle is targeting AU itself. Source cancellation remains an auxiliary route.
Do not assume a
common linear order for a circular strong component or infer HRV transport
from deletion coverage alone. No full component proof is claimed.

## Packet results and failed shortcuts

`COMPONENT_LEAF_PACKETS.md` proves full source cancellation for movable-leaf
packets and the coefficient of t^(n-1) for EVERY complete component via star
transport. `COMPONENT_BRIDGE_PACKETS.md` proves attached-chain cancellation and
five-flip attachment transport within one component. Its extension to a whole
internal component is the explicit open marked-ideal identity (Ideal).

A chain packet can satisfy (Src) while its coloring sum is nonsymmetric:
its source restrictions are not complete smaller-component sums. In the exact
four-vertex obstruction, source-boundary completion adds three states, stops
at seven of the eight target states, and introduces defect H_2(2t e_1+t^2).
The missing outgoing star cancels it, but all its flips involve its only source.
A proof must control cancellation and closure together.

Other checked boundaries remain in the modular notes:

- `DIAMOND_STRAIGHTENING_AUDIT.md`: fixed-diagram straightening is refuted;
  auxiliary diamonds and swaps need a controlled exterior correction.
- `COMPONENT_SOURCE_BRANCHING.md`: critical-fork normalization preserves HRV
  but is nonconfluent; conditional near-symmetry does not identify coefficients;
  the Claude local-pair proposal omitted an exterior defect.
- `COMPONENT_SINK_BRANCHING.md`: root-only promotion and fixed sink-priority
  arguments fail; the exact deletion defect and reconstruction survive.

## Current checks and computation

The new Rust diagnostic checks (StrongSrc) on every projected DAG in U_n for
n=1,...,5. All 1, 3, 25, 543, 29281 states, in respectively
1, 3, 22, 367, 13681 strong components, have zero formal defect. A separate
union-cycle check returns the exact three-state n=4 counterexample. The JSON
results were inspected; harness success is not treated as theorem evidence.
The new note records source hashes and logs. This is finite evidence only.

Six fixed larger circular seeds gave five complete strong components with
zero defect (12,979 states); one n=7 component exceeded 20,000 states and is
inconclusive. All selected trees through n=5 also had acyclic component unions;
the general compatible-lift proof now establishes this property independently.
The exact inputs, counts, code hashes, and receipts are in the ambient note.

The external probe reuses `circular_highest_reachable_vertices` from the shared
Rust library. Its owning directory is
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`.
The prior probes are retained as `component_source_probe-at-c6305a0.rs` and
`component_source_probe-at-73535cd.rs`.
Luna's snippet was reviewed and only its projected reachability predicate was
adopted; primary retained the original lifted-flip checks. No shared Rust source
or reusable polynomial family was added. The pending maintained integration
proposal is `suggestions/flip-enumeration-api.md`.

Prior exact evidence remains documented: all ordinary internal attachment
packets through five vertices pass; 458 full small components were cross-checked;
21 of 24 n=5,...,8 samples pass (27,836 states), with three capped/inconclusive.
These checks establish only their stated finite cases.

This increment changes documentation and an external diagnostic only. No Lean
source/build, immutable reference, Overleaf source, dependency, or shared Rust
source changed. Whitespace checks pass. The user-requested obsolete circular
plan was already removed at `ebfd5cc`.

The bounded active-corner screen reuses `probe.model`; a fresh Rust capability
check found no maintained flip enumerator. Exact hashes and counts are in
`COMPONENT_ACTIVE_CORNERS.md`. No new polynomial generator was introduced.

## Consultations and archive

Current task: Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`c2a21316-805d-489f-a1c7-40f51b40b57c`. Its full ordinary structural target is
`ORDINARY_ACTIVE_TARGET.md` in the external `projected-source-companion/`
request directory. It asks for a proof or exact counterexample to AU, not
another proof of the supplied conditional implication or broad enumeration.
Native observer session `38474` follows this same task with a two-hour allowance;
the script passed `bash -n` and cannot submit or cancel. Its status/follow logs
have the `ordinary-active-` prefix. Observation failure does not justify a new
submission. No candidate has returned yet.

Previous task:
Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`e8b27b28-541c-4e91-a846-d4b0db50a739`, is COMPLETE_WITH_ERRORS. The request
asks for a general (StrongSrc) proof and supplies the checked reductions and
counterexamples. A first-order result is explicitly partial. No exhaustive
large searches or conditional wrappers are requested. The compatible-lift
theorem was supplied inline after independent review.

Native session `31446` observed this same task with a two-hour allowance;
the wrapper passed `bash -n` and reconnected without resubmitting. Its logs,
input notes/hashes, submission and steering receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/projected-source-companion/`.
Primary downloaded and read `final-PROOF.md`: the target and its first-order
part remain open. The return repeats the balanced reduction and supplies
partial tree connectivity, not the component formula. Archive and extracted
proof hashes are in `docs/ARISTOTLE.md`. No candidate is integrated.

Claude Sonnet finished without a general proof (native session 6592). Its
incorrect exterior-factor claim was corrected and independently checked.
Aristotle project `d4b3ddfe-0051-4f80-b222-4e9374badcb3`, last task
`ae0d9a91-dc02-4f53-97a9-3ed6f8034bcf`, is terminal COMPLETE_WITH_ERRORS;
its useful source-branching and conditional coefficient reductions were audited,
but it did not prove the companion. No returned compatibility patches were
integrated. `docs/ARISTOTLE.md` retains task IDs, payloads and hashes.

Detailed research chronology and earlier ownership are archived in
`docs/archive/flip-component-checkpoints-through-c6305a0.md`. That file is
historical, not the current worker/task status. Older aggregate implementation
history remains in Git and the circular checkpoint archives. The ordinary and
aggregate circular completion audits remain authoritative for proved results.

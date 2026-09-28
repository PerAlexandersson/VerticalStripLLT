# Leftmost NN and general-transfer checkpoints

Archived at the incoming-transfer checkpoint. Later proof notes supersede
open claims only in their explicitly stated scope.

## Current general transfer and terminal-family checkpoint

2026-09-28, continuation from clean pushed `8bb43ca`; the previous goal
turn made proved progress. The requested full combinatorial recurrence
proof remains active. This increment strengthens a local move, proves a
new incoming-bridge case, and identifies terminal families of arbitrary
rank. It does not close the general NN/DN/DD or circular recurrence proof.

[Outgoing transfer](../proofs/COMPONENT_RIGHT_ARM_TRANSFER.md) now holds
for ANY ordinary connected unicyclic selected state with ac,bc,ad selected,
ab,bd absent, a<b=a+1<d<c. The retained ac need not be maximal or strict;
NN geometry and saturation are unnecessary. A backward bypass sweep
replaces the old tree-normalization bridge argument. Every exchanged
edge lies inside selected ac and cannot be strict. In the covering-bridge
case the attached component may contain the cycle, so we do not call it
a tree. All other endpoint edges are restored.

[Incoming bridge corollary](../proofs/COMPONENT_FOUR_CYCLE_SWAP.md):
in saturated eligible NN, if the cycle uses f or r, a bridge ta may
be moved to tb with every other edge restored. Normalize the remaining
cycle while lifting with the attached tree, apply the four-cycle branch
transfer in the full diagram, then undo. A containing strict corner
inside that tree remains present throughout. Incoming edges ON the cycle
remain open; 64 exact tests through n6 (49 on-cycle) and the n7 shield
fixture pass, but are not a proof. The n9 counterexample still excludes
incoming transfer without the condition on the cycle.

[Path-square terminal family](../proofs/COMPONENT_PATH_SQUARE.md):
for area(0,1,2,...,2), all selections with k adjacent normal edges form
one complete component, via 10↔01 moves. Aggregate coefficient extraction
proves its HRV formula; a direct fiber count gives an explicit elementary
expansion. The component survives iff k≤floor(n/2), and for k≥1 has
cycle rank k−1. This supplies surviving terminal cases of unbounded rank.
It also disproves automatic leftmost NN eligibility after reversal and
articulation: the strict terminal gap fails (2<2), while boundary equality
actually holds. The eligible DD triple is the terminal translate, not
necessarily 02,13,24. The family is solved, not an unresolved counterexample.

Primary and existing Astra simpler_component_route independently audited
the mathematics and final notes. Exact transfer checks enumerate every
ordinary natural graph through n7 and all connected unicyclic selections,
including nonsaturated envelopes and nonmaximal retained edges. At n7:
429 graphs,381430 states,10609 component occurrences,96554 transfers.
All path-square components for n3–12 also pass. Final commands exit0.

Frozen sources/model, Cargo files, commands, independent review, receipts
and hashes: `/lake-cache/ai-projects/requests/VerticalStripLLT/adjacent-transfer/`.
Primary owns notes/index/handoff and external consumers, retaining the
sole serialized Lean build slot. All owned processes and bounded reviewer
assignments are terminal. No new worker/account, Claude process, Lean build,
manuscript or maintained Rust edit. Runtime/MCP and Rust capability checks
were refreshed; Lean MCP remains rooted in RealRooted and unused. Existing
flip-enumeration API integration proposal remains. Previous timed-out Claude
call is recorded in the preceding checkpoint; no conclusion was adopted.

Next: prove the incoming ON-cycle transfer under the NN f/r-cycle condition,
or close the DN/DD joins directly. A general-a middle-image contraction
would need incoming transfers and cannot silently use the false unrestricted
statement. Leftmost NN alone has no proved coverage theorem. Uniform leaf
envelope restoration in surviving unicyclic components is still open.
The full objective includes higher ranks and cannot be replaced by these
terminal cases or the already completed Lean word proof.

## Current leftmost NN checkpoint

2026-09-28, continuation from clean pushed `5ddde49`. The full requested
recurrence/diamond component proof remains active. This checkpoint proves
its **leftmost NN step for connected unicyclic components**, not the full
NN/DN/DD induction or higher cycle ranks. The completed Lean word proof
remains separate and is not completion of this requested route.

New [leftmost NN proof](../proofs/COMPONENT_LEFTMOST_NN_UNICYCLIC.md):
no packet contains two surviving connected unicyclic components. The
packet identity therefore writes each surviving component as a sum of
whole smaller target components minus whole tree corrections, with
identical coefficients for K and E. The proof connects all middle images
of one tree envelope by adjacent contraction. Forced reachability extends
to any prescribed forest containing the maximal intervals. Two explicit
paths handle the exceptional middle join; inactive-f components have zero
or one surviving neighbor. Actual target-cover hypotheses justify the
first join's q-introduction. Delete f to obtain a tree only after assuming
f redundant; the covering case is handled first.

New [outgoing transfer](../proofs/COMPONENT_RIGHT_ARM_TRANSFER.md):
B∼B−ad+bd for every connected unicyclic NN state selecting f,r,ad
and omitting q,bd, b<d<c. Bridge normalization and three explicit cycle
cases fix every other edge. At a=0 this proves unrestricted q-free σ
invariance. The incoming analogue is false, with a checked nine-vertex
counterexample whose distinct inactive components have different tree
envelopes. The [block note](../proofs/COMPONENT_UNICYCLIC_BLOCKS.md)
also proves full-envelope leaf restoration for components inactive at
a strict corner other than the leftmost one; survival remains open there.

Primary and existing Astra simpler_component_route independently audited
the proofs and final written argument. Reviewer corrections above are
incorporated. Exact checks pass: 555 outgoing transfers in all 76 eligible
NN instances through n6, plus two n7 fixtures; all 41 leftmost instances
through n6; two further n7 leftmost fixtures (no distinct joins); paired
local paths n5–9; and all 132 articulation-free saturated n8 diagrams for
the inactive-corner leaf assertion. Final commands all exit0.

Frozen sources/model, manifests, commands and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/leaf-envelope/`.
The tool-free Claude leaf-envelope consultation ended at its 20-minute
cap, exit124, with no final result. No Claude conclusion is adopted.
Request/stream/status are retained; owned PID42854 is absent. All compiler
sessions and the existing Astra assignment are terminal.

Primary owns the notes/index/handoff/archive and external consumer, and
retains the sole serialized Lean build slot. No new worker/account, Lean
build, manuscript edit or maintained Rust edit. Runtime registry/MCP and
Rust capabilities were refreshed; Lean MCP still targets RealRooted and
was unused. The existing flip-enumeration integration proposal remains.
Verification is mathematical review, exact finite assertions, receipt
hashes, documentation links and diff checks. No Lean claim is added.

Next: extend the recurrence method to leftmost DN/DD and larger cycle
ranks, or prove a reduction that avoids those cases. General-a incoming
transfers must not be assumed: the counterexample above excludes them.
[Archived swap/block checkpoints](component-recurrence-handoff-through-blocks-20260928.md)
retain the preceding arguments, unresolved routes and evidence.


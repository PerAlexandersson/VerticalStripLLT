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



## Incoming-transfer and inactive-correction checkpoint d77a68f

2026-09-28, continuation from clean pushed `e750bd9`; preceding goal turn
made proved progress. The requested general combinatorial component proof
remains active and incomplete. No Lean or manuscript work in this increment.

New [incoming transfer](docs/proofs/COMPONENT_INCOMING_EDGE_TRANSFER.md):
if t<a<b=a+1<v<c, A selects f=ac,r=bc,ta,tv, omits q=ab,tb, and
its connected unicyclic graph has its cycle on f or r, then ta→tb
is achievable with every other edge restored. Four cases: bv selected;
plain three-stage transfer; break a t→b bypass by tx→xv; break a
b→v bypass by bx→xc. Restore the bypass only after moving the incoming
edge. This local theorem needs neither saturation nor NN eligibility.
A containing corner uv with u<t does NOT supply selected tv; that
remaining case must not be assumed solved.

New [general NN corrections](docs/proofs/COMPONENT_NN_INACTIVE_CORRECTIONS.md):
for EVERY eligible saturated NN position, each inactive-f connected
unicyclic component is isolated or has exactly one surviving neighbor.
The skipped-b case is now proved. All redundant-f middle images of one
fixed tree envelope connect: first transfer incoming BRIDGES, then
outgoing edges, and apply tree connectivity after contracting q.
Incoming edges are bridges because their cycle is inside [a,c]. First
left joins therefore use the already-proved bridge lemma, not the still
open unrestricted incoming transfer. Inactive vertices cannot connect
two different survivors through a packet path; direct active joins remain.

The same note proves every RIGHT q-exit that first makes f cover connects
the original middle pair. The previous d<e paths extend to any a. For
e<d, a seven-stage path (two outgoing-transfer macros) restores every
edge. A q-preserving first-cover transition also lifts. Neither statement
handles arbitrary runs of q-free states or the left q-exit, so general
f-active middle/first isolation remains open. DN/DD, recurrence coverage,
higher ranks and the full circular route also remain part of the goal.

Primary and existing Astra simpler_component_route audited all statements
and final written proofs. Reviewer corrections incorporated: require
Env(T)=H explicitly; retained ad covers while redundant f does not, hence
d<c before applying the unique-cycle argument. No result attributed to
Claude in this increment; the previous timed-out call had no adopted result.

Checks: four selected-tv cases appear 19/36/1/1 times through n6 and
20/57/4/0 in the n7 shield fixture; all nonmacro flips checked directly,
outgoing macros checked against whole-component membership. General NN
inactive families through all 76 n≤6 instances: skipped-b27, length-two22,
longer-through-b19; n7 shield adds one skipped-b component. Every required
neighbor assertion passes. Expanded e<d paths n5–9 use11–19 actual flips.
Final commands exit0; no failed mathematical assertion or compiler run.

Frozen sources/model, Cargo files, exact commands, review, receipts and
hashes: `/lake-cache/ai-projects/requests/VerticalStripLLT/incoming-transfer/`.
Primary owns notes/index/handoff/archive and the external consumers;
sole serialized Lean build slot retained. All owned processes and bounded
agent assignments are terminal. No new worker/account, Claude process,
Lean build, manuscript edit or maintained Rust edit. Existing Rust API
integration suggestion and Lean-MCP/RealRooted routing limitation remain.

Next: handle incoming on-cycle edges without selected tv, or left q-exits
and longer q-free paths in active-middle comparison. The all-inactive
correction theorem now separates that issue cleanly. Do not infer a
complete proof from the solved path-square family or the Lean word proof.
[Archived leftmost and transfer checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain the preceding proofs, review boundaries and finite receipts.



## Leftward-transition checkpoint 6195af1

2026-09-28, continuation from clean pushed `d77a68f`. The previous
status-only turn made no durable progress; this turn proves a new local
step and narrows the active-middle gap. The requested full combinatorial
component proof remains active and incomplete.

New [leftward NN transition](docs/proofs/COMPONENT_LEFT_EXIT.md): every
left q-exit exposing redundant f in a connected unicyclic saturated NN
state connects its middle pair. Choose a containing strict corner uv.
The same attached tree reduces to the rightward lemma by tree connectivity
on two adjacent attachment vertices. A head on the bypass gives a
three-flip repair. A different attached tree moves to an earlier bypass
vertex until it exposes f or gives an incoming tail u<t. Strong induction
on t closes the latter case. The local normalization may lose q; its
endpoint restores q, and the deleted-f envelope stays fixed.

A further proposition closes the active middle join whenever F=M+q
forces a→c but the maximal-edge forest M does not. A maximal interval
containing q supplies either an outgoing bridge, or a crossing strict
corner uv; F+ub is then a forest and gives an incoming bridge. Apply
the rightward or new leftward lemma and redundant-middle-image connectivity.

Remaining: when F does not force the bypass, a q-selected f-covering
tree exists, but its comparison with redundant middle images is unproved.
A sufficient next assertion is that some redundant q-selected tree of
the same envelope has a flip immediately exposing f (q may be removed).
Do not assume q-preserving tree connectivity: even an eligible K5 NN
example in the note refutes it. General first joins, DN/DD, recurrence
coverage, higher ranks and the full circular recurrence route remain.

Primary and existing Astra `simpler_component_route` independently audited
the written lemma and proposition. Reviewer scope corrections incorporated:
state connected/unicyclic explicitly; identify maximal containers in the
original diagram. No Claude result used in this increment.

Checks: direct actual flips pass three local repairs (3,7,3 moves) and a
two-move smaller-tail preparation plus its exposing exit. The first harness
wrongly asserted q survived the deliberate q-exit; corrected without
changing the proposed flips. Final run exits0. The exposure assertion has
finite evidence in all 55 relevant envelopes across 76 NN instances n≤6
(211 states,192 immediate exposures); n7 shield gives5/72/61 and n7
three-corner gives3/28/18. These are evidence, not a uniform proof.

Frozen consumers/model/manifests, commands, review, receipts and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/left-exit/`.
The external consumer reuses the existing cover model and Rust APIs;
maintained Rust HEAD remains d53fb193af3c69adedbd9ec8592f87235d809ffa.
No maintained Rust edit or polynomial generator. Runtime registry and
`codex mcp list` rechecked; Lean MCP still routes to RealRooted and is
unused. Existing integration/routing suggestions remain applicable.

Primary owns notes/index/handoff/archive and external consumers and retains
the sole serialized Lean build slot. No Lean build or manuscript edit,
new worker/account, or Claude process. All compiler checks are terminal.
The existing Astra assignment finished read-only and build-free; ownership
is released and no owned process remains live.
[Archived preceding checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain incoming transfer, inactive corrections, leftmost NN, and path-square
proofs with their exact verification boundaries.


## Current general NN middle-join checkpoint

2026-09-28, from clean pushed `6195af1`; preceding turn made verified
progress. The requested combinatorial recurrence proof remains active.
**User scope correction:** focus on ordinary components. A circular
extension is optional, not a completion requirement, and is not inferred
merely from locality. The completed separate Lean theorem remains intact.

New [general NN middle joins](docs/proofs/COMPONENT_NN_MIDDLE_JOINS.md):
every f-active middle join is internal for connected unicyclic states
at any eligible saturated ordinary NN position. For T=A−f, H=Env(T),
M its maximal intervals, F=M+q, the F-forcing case uses the preceding
left/right exit proposition. Otherwise choose e=xy on the increasing
bypass outside F and maximal g=uv containing it. In Z=F∪P, remove e.
If g is on the a-side, reconnect by uy; on the c-side, reconnect by
xv; in a third component, adjoin xv to Z. Each prescribed forest
extends to a tree of H with a q-preserving exposing flip. The no-head
NN condition makes the F-component of a point outward; other F-components
are increasing chains. This supplies the increasing detours. Same-envelope
tree connectivity and redundant-middle connectivity finish the theorem.

First-join reductions in the same note: a cycle in another natural block
leaves a tree comparison in the f-block; an outgoing cycle edge at a/b
can be moved to put the cycle on f,r. A sink with an incoming cycle
edge ta and selected tv, b<v<c, reduces to the outgoing case in one
or two flips. The seven-vertex surviving sink fixture is covered by this
last lemma. Arbitrary cycles within the f-block avoiding a,b, and sinks
without such a selected containing edge, remain. Left first joins also
need their incoming held-edge repairs. DN/DD, recurrence coverage and
higher cycle ranks remain; do not claim full NN or the ordinary theorem
by this route yet.

Primary derived the exposure construction; existing Astra reviewer
simpler_component_route independently audited it, the written theorem,
the first-join reductions and sink preparation. No flaw or correction
found. Assignment completed read-only and build-free, ownership released.
Primary owns notes/index/handoff/archive and the external consumers and
retains the sole serialized Lean build slot. No new worker/account,
Lean build, maintained Rust edit or manuscript edit.

Verification: actual forest constructions pass all 76 eligible NN
instances n≤6 with counts [107,86,25] (a-side,c-side,third component);
n7 shield [12,48,0], n7 three-corner [17,12,16]. Each check extends the
forest, checks membership in the original COMPLETE source component,
checks the actual flip, preservation of F and exposure of f. Every
final Cargo command exits0. The seven-vertex first-join fixture has an
11-flip BFS path; the two-flip sink preparation and its adjacent-swap
image both pass direct cover checks. This is supporting finite evidence
for the independently audited proof, not a substitute for it.

External sources, receipts and consultation:
`/lake-cache/ai-projects/requests/VerticalStripLLT/middle-exposure/`.
Maintained Rust HEAD remains d53fb193af3c69adedbd9ec8592f87235d809ffa;
consumer reuses existing actual-flip and graph APIs. No polynomial family
or generator was introduced. Existing API-integration and Lean-MCP routing
suggestions remain applicable. Compiler processes are terminal.

The primary-owned tool-free Claude exposure consultation reached its
20-minute cap with exit124 and no final result. Its exact owned PIDs are
absent; native session41177 is terminal. The stream was producing thinking
events, not a completed proof. No result is attributed to Claude. All
owned processes and reviewer assignments are now terminal. Frozen sources,
review, exact commands, receipts and SHA256SUMS are in the request folder.

[Archived preceding checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain leftward transitions, incoming transfer, inactive corrections,
leftmost NN and path-square proofs with their verification boundaries.


## Current first-join tree comparisons

2026-09-28, from pushed `77913ae`. The requested combinatorial recurrence
proof remains active. **Required scope: ordinary components only.** The
user considers the circular extension optional; locality is not a proof
of that extension. The existing separate Lean theorem remains intact.

New [first NN joins](docs/proofs/COMPONENT_NN_FIRST_JOINS.md): a tree
path with fixed exterior lifts whenever the exterior meets the local
vertices at at most two attachments with no directed path between them.
This lemma allows arbitrary exterior cycle rank. For connected unicyclic
first left joins whose cycle avoids a,b, the least selected incoming
tail makes the two attached trees have the same envelope. More generally,
adjoin a covering cycle edge incident to the attachment root: the
remaining cycle path has no directed connection between the two ends.
Equal envelopes of these enlarged trees then prove the first join.
The same criterion repairs an incoming bridge away from the cycle.

The n10 nonleast-tail first join and n9 remote-cycle bridge examples
both satisfy this enlarged-tree criterion. Their original attached-tree
envelopes differ; after adjoining the strict cycle corner they agree.
The known inactive example fails precisely because the exterior has a
directed path across that corner. Survival alone has not been proved
to provide a suitable covering edge incident to the attachment root.

The preceding [middle-join theorem](docs/proofs/COMPONENT_NN_MIDDLE_JOINS.md)
settles all middle joins in cycle rank one. General first joins, DN/DD,
recurrence coverage and higher cycle ranks remain. Do not claim the full
ordinary component recurrence proof from these partial results.

Verification: exact local searches produced paths of 11 and 10 actual
flips in the n10 and n9 examples. All 12,109 and 1,665 traversed local
flip tests agree with the original full diagrams. Correct envelope
maxima and the inactive failure were checked explicitly. Final Cargo
command exits0. These finite checks support the general arguments.
Primary and the existing Astra reviewer independently audited the
criteria and the final written note. The written audit passed without
further corrections, including both corrected fixture maxima.

Primary owns the new note/index/handoff/archive and external consumers,
and retains the sole serialized Lean build slot. Existing Astra
simpler_component_route completed the bounded read-only, build-free
written-note audit and released ownership. No new worker/account, Claude process, Lean build,
maintained Rust edit or manuscript edit. Compiler jobs are terminal.

Frozen sources, exact command, receipts and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/first-join-tree-lifts/`.
Maintained Rust HEAD remains d53fb193af3c69adedbd9ec8592f87235d809ffa.
No polynomial generator was introduced. Existing flip-API integration
and Lean-MCP routing suggestions remain applicable. Earlier owned Claude
consultations are terminal; no Claude result is used here.

[Archived preceding checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain general middle joins, left/right transitions, inactive corrections,
leftmost NN and path-square results with exact verification boundaries.


## Current general incoming-bridge checkpoint

2026-09-28, from clean pushed `e7ea36e`; preceding turn made verified
progress. The requested combinatorial recurrence proof remains active.
**Required scope: ordinary components only.** Circular is optional.

Extended [NN tree comparisons](docs/proofs/COMPONENT_NN_FIRST_JOINS.md):
an incoming bridge ta can be replaced by tb in a connected unicyclic
saturated NN state selecting f=ac,r=bc and omitting q=ab, when the
cycle avoids f,r and a selected STRICT COVERING corner contains ta,tb.
The container may be anywhere: in the same attached tree, on the cycle,
or in another attached tree. This removes the previous attachment-root
restriction and the different-tree obstruction for this bridge move.

Proof: remove a spare cycle extremum and use two-attachment tree lifting.
Without a spare extremum, normalize a COMMON connector (cycle on t-side)
or a common core using the prescribed forest M+q. This puts the changed
attachments behind one bridge. Slide that bridge across a covering cycle
edge, or expand the cycle through it; the old root becomes available for
the cut. For a container in another tree, either the same normalization
points inward, or an endpoint of the container points outward from the
changed root and inward from its own root. Normalize and move that tree
instead. If the first stem is the strict container itself, expansion
puts it on the cycle and reduces to the preceding case.

The theorem requires a covering container, not merely a strict one.
Saturation plus mixed acyclicity of the INDIVIDUAL STATE supplies it.
Together with the earlier cycle-on-f/r result, this proves incoming-bridge
transfer for any mixed-acyclic connected unicyclic saturated NN state
selecting f,r and omitting q. Membership in a component with some
mixed-acyclic representative is not sufficient for that corollary.
A further audited corollary now gives B∼σB when the unique cycle avoids
a,b and B is mixed-acyclic: transfer the incoming/outgoing bridges one
pair at a time. Each endpoint preserves the cycle and mixed acyclicity;
intermediate macro paths need not do so. Both first NN joins are then
internal under these same state hypotheses, by two bridge preparations,
the swap, and a final incoming/outgoing held-edge repair. First joins
with a cycle meeting a or b as a sink, arbitrary component representatives,
DN/DD, recurrence coverage and higher ranks remain. Do not claim the full
component recurrence proof.

Primary and existing Astra simpler_component_route independently audited
the cycle-corner proof, both common normalization constructions, the
other-tree argument, full swap/first-join consequences, and final written
statements. Final audits pass with
no outstanding correction. All eight exact fixtures pass: local path
lengths [12,13,10,6,8,14,15,15], with 311,990 local/full actual-flip
comparisons and strict-corner retention assertions. Seven fixtures also
check paired preparations of [2,1,1,2,1,1,1] flips per endpoint. Checks
include a core rooted at c, q normalization, both bridge orientations,
and a strict containing edge entering the cycle. Final Cargo command
exits0; these are finite checks supporting the uniform proof.

Primary owns the note/index/handoff/archive and external consumer and
retains the sole serialized Lean build slot. Existing Astra audit is
complete, read-only/build-free, ownership released. No new worker/account,
Claude process, Lean build, maintained Rust edit or manuscript edit.
All owned compiler processes are terminal.

Sources, commands, audit, receipts and hashes are frozen under
`/lake-cache/ai-projects/requests/VerticalStripLLT/cycle-path-tree-lifts/`.
Maintained Rust HEAD remains d53fb193af3c69adedbd9ec8592f87235d809ffa;
capability guide/metadata/source checks were renewed. No polynomial
generator was introduced. Runtime registry and `codex mcp list` checked;
Lean MCP still routes to RealRooted and is unused. Existing API-integration
and MCP-routing suggestions remain applicable. No Claude result used.

[Archived preceding checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain the first tree criteria, general middle joins and earlier results
with their verification boundaries.



## Sink repair checkpoint 4288406

## Current NN sink repair and direct component bookkeeping

2026-09-28, from clean pushed `b343045`; preceding turn made verified
progress. The combinatorial proof goal remains active, ordinary only.
**Latest user direction:** push ONE component through the recurrences,
repair/identify the pieces on the other side, and collect whole smaller
components. Keep this construction central. Packet isolation is only a
sufficient alternative, not an extra goal or requirement.

New [sink repair](docs/proofs/COMPONENT_NN_SINK_REPAIR.md) proves B∼σB
for every connected unicyclic saturated NN state selecting f,r, omitting
q, whose cycle avoids f,r and meets a or b as a sink. No mixed-acyclicity
hypothesis is needed for this theorem. Choose a strict container of an
incoming cycle edge. If it is on the cycle, a suitable cycle minimum
permits equal-envelope tree comparison replacing a contained incoming
edge by av. Freeze the f,r,b tree outside to keep q absent. For a corner
in an attached tree, root normalizations and bridge slides/expansions
reduce to such a cut. The difficult decreasing-arc loop terminates by
moving the root one edge towards a. The b-branch macro has a separately
proved swapped-endpoint connection; do NOT conjugate its interior path.
The tree-lifting lemma now allows any number of exterior attachments,
provided there is no directed exterior path between distinct ones.

The [direct NN note](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md) now
puts the single-component indicator h and its transported coefficients
back at the center. Both left/right q-exchanging overlaps have
Δ0=h10(P)−h01(P), Δ1=h01(Q)+h01(P)−(h00+h01)(σQ).
All q-preserving target flips already have equal initial coefficients.
The repair must have zero K and E valuation and produce coefficients
constant across ALL target flips, after which they are whole-component
coefficients. Local repairs may disturb other boundaries. This is still
an open uniform construction, not a completed component recurrence.

The sink theorem supplies a needed identification, but it does not by
itself supply every held-edge repair, every component representative,
DN/DD, higher ranks or recurrence coverage. Next work should track the
remaining Δ coefficients for ONE component and repair/collect them;
avoid turning all possible auxiliary connectivity statements into new
requirements before doing that bookkeeping.

Primary and existing Astra simpler_component_route independently audited
the full sink argument, final written proof, and direct coefficient
section. All final audits passed without an outstanding correction.
Verification: all76 eligible NN instances n≤6 pass the complete-component
sink swap check, with counts [2,2]; n7 area0123432 adds [2,2]. The n7
three-corner fixture has no qualifying states. Three local tree cuts on
8,11,10 vertices give paths of3,5,5 flips and36,170,341 local/full cover
comparisons. Every original strict corner is retained; b is omitted from
local vertices, so the paths stay q-free. These are supporting finite
checks, not checks of every branch construction. Final Cargo runs exit0.

Primary owns sink/first-join/direct-NN/middle-join notes, index/handoff/
archive and existing external consumers; sole Lean build slot retained.
Existing Astra reviewer completed its read-only/build-free assignments
and released ownership. No new worker/account,
Claude process, Lean build, shared Rust edit or manuscript edit. All
owned compiler processes are terminal.

Frozen sources, receipts, commands and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/sink-recurrence-repair/`.
Maintained Rust HEAD d53fb193af3c69adedbd9ec8592f87235d809ffa; capability
checks/metadata renewed. No polynomial generator introduced. MCP list
rechecked; Lean MCP still routes to RealRooted and is unused. Existing
API-integration/MCP-routing suggestions remain applicable. No Claude
result used in this increment.

[Archived checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain general incoming bridges, earlier first joins and middle joins.


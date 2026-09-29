# VerticalStripLLT handoff

## Current continuation — maximum simultaneous-corner layer proved

Primary resumed from clean pushed `f27da0d`; this turn made verified
progress. The full goal remains active: prove the ordinary non-circular
component expansion by the author's four diagram recurrences. The separate
completed Lean word-functional theorem is NOT an input. The user excludes
fundamental-basis calculations and wants whole-component tracking through
diamonds and endpoint relabeling.

**New proved uniform cyclic case:** the
[simultaneous-corner theorem](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously)
and its [DN recurrence](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-at-the-maximum-simultaneous-corner-layer).
Let M be ALL maximal natural edges. The short pairs ab->bc belonging
to corners ac form disjoint directed paths of lengths l_j. The largest
edge count with all corners selected and covering is
m*=|M|+sum ceil(l_j/2). At equality every path has a maximum nonadjacent
selection. Choose an available forward move at the largest corner head,
then the smallest middle vertex. All later available moves have lower
priority. If this move destroyed a cover, following its bypass would
force a higher-priority available move, a contradiction. Thus it is an
actual flip retaining every corner cover. Repeating reaches the last-node
alternating selection, which itself always covers all corners.

Hence exactly ONE whole component C* in that layer has a simultaneous
cover state. Every other component deletes an absent corner or uses the
proved alternating corner-deletion recurrence. These are independent
whole smaller-component expressions, so full-layer subtraction gives
complete NN and DN recurrences for C*. Every component above m* also
reduces. Arbitrary crossing exterior and unmarked corners are allowed.
This extends the preceding one-corner dense bound, whose proof remains
in the notes at `b861fb7` and receipt `dense-corner-layers-20260929/`.

**Verified:** graph-only `--corner-capacity`, 14 NN/DN fixtures:
7911 simultaneous-cover states, 63 maximum states connected by 110
prescribed actual flips. The recurrences account for 7818 source states,
364 actual-target components / 11787 states, 64 absent-corner corrections
/ 3075 states, and 269 alternating corrections / 894 states. Every
alternating image partitions into whole components (1733 terms), with
4404 surviving-bypass checks. Every final diagram is strictly smaller.
The separate `--corner-normalization-scan` checks 148 diagrams on 7--9
vertices, 1,274,304 source states, 192715 simultaneous-cover states and
1098 maximum states normalized by 2401 prescribed actual flips.
Both runs exited zero with empty stderr. No Lean build was run.

Frozen sources, commands, logs and checksums:
`/lake-cache/ai-projects/requests/VerticalStripLLT/joint-corner-capacity-20260929/`.
The external diagnostic edge cap is now 21 (component cap unchanged at
20000), for the nine-vertex cube fixture with 21 natural edges, five
strict corners and only 65536 legal source states. Maintained Rust is
unchanged; this does not authorize larger or unbounded scans.

## Remaining proof obligation

General NN/DN collection in LOWER cyclic layers k<m* remains unproved.
Below maximum path occupancy, a forward move may create an available
move to its RIGHT; the decreasing-priority proof fails. Do not infer
arbitrary-layer uniqueness from the new theorem or previous scans.
Every extra source component still needs its independent reduction.
Direct RHS diamonds remain an allowed alternative to source completion.

Continue with connected cyclic full-envelope components after the proved
weak-block, absent/inactive-corner, fixed-short and tree reductions.
The 125-state eight-edge NN component in area 012333 now has m*=9,
and the 3381-state eight-edge component in area 0123434 has m*=12.
Both remain open. The 77-state nine-edge component of the first diagram
and the 2305-state twelve-edge component of the second are now solved.
The connected 4998-state DN component at m*=15 in area 012333333 is
also solved (the older one-corner bound was 19).

## Lower-layer continuation — temporary redundancy is necessary

The [six-vertex obstruction and chain normalization](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners)
are now proved. In area 012333, write M={03,14,25}. The states
A=M+{01,02,12,34,45} and B=M+{01,12,34,35,45} cover every corner,
but A has NO actual neighbor doing so. Its four possible flips each
make another corner redundant. Nevertheless six corner-retaining flips
join A to B, with 14 redundant at all five intermediate states. Both
states are already chain-normalized anchors. This is an exact obstacle
to requiring simultaneous covers along a lower-layer path, not a
counterexample to connectivity or the component recurrence.

A uniform preparation theorem now allows this temporary redundancy:
process entire corner chains in decreasing maximum order; repeatedly
flip their smallest-head exit into an incoming edge. The current
chain's corners remain covers. At completion the processed union is
absorbing, so all other corners recover their covers. The explicit
endpoint keeps increasing-chain-max normals and replaces each inversion
vy by yh, with h the strict successor of v. Thus EVERY simultaneous-cover
state reaches a mixed-acyclic anchor by actual flips, even if initially
mixed-cyclic. Endpoint constancy and lower-layer collection are NOT proved.
Use this diagram path theorem only; do not reintroduce basis calculations.

Graph-only `--joint-chain-normalization` passes all 7911 states in the
14 fixtures, including 328 initially mixed-cyclic states: 10877 actual
flips and 593 intermediate redundant states, with every block invariant
and explicit endpoint checked. `--corner-occupancy` verifies the six-flip
obstruction. Its 1017 same-occupancy groups have 1022 all-cover pieces;
allowing temporary redundancy merges the pieces in every tested group.
This last observation is finite evidence, NOT a general connectivity
lemma. Both runs exited zero with empty stderr. Frozen sources and logs:
`/lake-cache/ai-projects/requests/VerticalStripLLT/lower-corner-normalization-20260929/`.

## Established reductions to retain

- [Outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md) and
  [notebook map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md): the four recurrences,
  paired middle diamonds, identity sectors and whole-exterior endpoint maps.
  DD/ND inheritance and the first-drop induction order are proved.
- [Fixed terminal short](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction):
  all fixed-r components reduce, including arbitrary incoming DN exterior.
  Fixed-q cases are proved too. The remaining general case has both varying.
- [No joint short selection](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#pairing-the-middle-states-when-joint-selection-is-absent):
  every 01 state has both arms as bridges and its exact-exterior 10 mate.
  This is one-way pairing, not a full recurrence for that class. All 66
  tested examples already reduce by blocks, smaller envelope, trees or
  inactive corners; their seven raw-image boundaries are not new open cases.
- [Arbitrary source trees](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#full-layer-recurrence-for-arbitrary-source-trees):
  complete NN/DN recurrences, including unsaturated sources. Extra source
  layer components either delete a missing corner or become one whole
  smaller component by concatenating their induced weak-block diagrams.
- [Endpoint attachments](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit):
  proved for endpoint-preserving recurrences. The earlier 84-state NN and
  coupled 69/126-state examples also have completed recurrences and their
  stated attachment extensions. They do not settle arbitrary crossings.
- [DN through an empty corner](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram):
  a general eligible NN collection theorem, allowing empty unmarked corners,
  would settle DN. Do not induct on the larger auxiliary NN source itself.

## Ownership, restrictions and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, the earlier authorized endpoint/source-addition continuations,
and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
The primary also owns the pre-dense handoff archive linked below. Preserve
all other file ownership and all earlier proof-note text as prefixes.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Keep any later authorized Lean work serialized under the primary build
owner. No worker/account/profile/model change has been made or requested.
Runtime registry, `codex mcp list`, Rust guide, Cargo metadata and existing
Graph/Poset/cover-flip APIs were checked. Lean MCP is rooted at RealRooted
and unused. Maintained Rust remains clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`.

The user-requested replacement began at pushed account-swap checkpoint
`2511182`. The complete prior handoff at `3151906`, with every intermediate
proof checkpoint, receipt and ownership record, is retained in the
[pre-dense-layer archive](docs/archive/component-handoff-before-dense-layer-20260929.md).
Only relative Markdown links were adjusted there. The older account-swap
history and original notebook/Overleaf paths remain available through it.

The maximum-layer proof checkpoint `c2c5a0d` is pushed to `origin/main`.
The lower-layer continuation preserves both proof-note prefixes at that commit.
The outline now removes the stale account-pause and unfinished-attachment
instructions and routes to the proved attachment theorem and current gap.
Both frozen receipt hash lists, local file links in the four edited files,
and `git diff --check` pass. No background job needs monitoring or restarting.

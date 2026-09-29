# VerticalStripLLT handoff

## Current continuation — the largest corner-active layer is proved

Primary resumed from clean pushed `3151906`; the preceding turn made
verified progress. The full goal remains active: prove the ordinary
non-circular component expansion by the author's four diagram recurrences.
The separate completed Lean word-functional theorem is NOT an input.
The user explicitly excludes fundamental-basis calculations and wants
whole-component tracking through diamonds and endpoint relabeling.

**New proved uniform cyclic case:**
[dense-corner NN recurrence](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-edge-layer-in-which-a-corner-can-cover)
and its [DN version](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#the-largest-f-active-dn-layer).
For strict maximal f=wz of length d=z-w in a natural graph with N edges,
put k*=N-d+1. A covering f requires at least d-1 absent edges: one from
each disjoint pair wi,iz. At equality every other natural edge is selected.
The absent arms must form a cut, and the d cut states connect by actual
flips retaining f. Hence there is exactly ONE f-active component C* at
edge count k*. Every other component in that layer, and every component
above it, deletes the everywhere redundant f to a whole smaller component.

The complete source-layer identity now isolates C*: NN gives target
layers k* and k*-1 minus those independent deletions; DN gives target
layer k* minus the deletions. In NN the r-selected deletion images cancel
whole target components exactly. All final terms are whole components in
strictly smaller diagrams, with the same K/E coefficients. Both q and r
vary on C*, so this treats a class of the remaining two-variable cases.
For complete natural graphs on n vertices, its cycle rank is
(n-2)(n-3)/2; the theorem is not bounded to small cycle rank.

**Verified:** graph-only `--dense-recurrences` checks all 13548 covering
states in 11 NN/DN fixtures, including the exact 32 cut states. The
recurrences have 296 source states, 91 positive components / 478 states
and 77 negative components / 182 states, after 93 whole cancellations.
All 170 same-layer deletion images and 110 higher-layer images are checked
with BOTH directions of their actual flip graphs. Every final diagram
strictly decreases the original induction order. Runs exited zero with
empty stderr; no launched process remains.

Frozen sources, commands, logs and checksums:
`/lake-cache/ai-projects/requests/VerticalStripLLT/dense-corner-layers-20260929/`.
It also retains the separate activity scan: 148 saturated diagrams on
7--9 vertices, without articulation and with at most 18 natural edges,
covering 1,274,304 states. No duplicate connected active components at
one edge count were found. The fixed articulation control reproduces
two. This is finite evidence for the old refinement, NOT a general
uniqueness theorem and NOT an input to the new dense-layer proof.

## Remaining proof obligation

General NN/DN collection in LOWER cyclic layers remains unproved. The
cut proof requires exactly d-1 missing edges. With additional missing
edges it does not classify the covering states or show that all source
additions independently reduce. Do not infer general active-component
uniqueness from the scan or promote source unions to a recurrence for C.
Direct RHS diamonds remain an allowed alternative to source completion.

Continue with connected cyclic full-envelope components after the proved
weak-block, absent/inactive-corner, fixed-short and tree reductions. Useful
explicit candidates in the previous receipt include the 125-state,
eight-edge NN component in area 012333 (k*=10), and the 3381-state,
eight-edge component in area 0123434 (k*=14). They pass the connected,
full-envelope, corner-activity and native mixed-acyclic filters; those
filters alone neither prove irreducibility nor supply a recurrence.

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
This checkpoint also owns the new handoff archive linked below. Preserve
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

Verification preserves both previous proof-note prefixes and the complete
archived handoff; 155 local file links, frozen receipt hashes and
`git diff --check` pass. No background job needs monitoring or restarting.
Proof checkpoint `b861fb7` is pushed to `origin/main`.

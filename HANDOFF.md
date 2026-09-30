# VerticalStripLLT handoff

## Current continuation — all-cover normalization to one sink per block

Primary resumed from clean pushed `f7c42d6`. The previous goal turn made
verified progress; so did this continuation. The FULL goal remains active:
prove ordinary non-circular component expansion by the author's four
diagram recurrences. Do NOT use the completed Lean word-functional theorem
or fundamental-basis calculations. Track one whole component, retaining
all exterior edges, and collect whole smaller components after diamonds
and permitted relabelings.

**New uniform component representative:** the
[quotient-fork normalization](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lifting-a-quotient-fork-and-obtaining-one-sink-in-each-block)
proves that EVERY ordinary component with a simultaneous-cover witness
contains an anchor with all maximal corners covering and one sink in each
weak block. This uses actual paths and preserves all strict edges and
selected-edge counts. The endpoint is not proved unique; this does not
complete general NN/DN collection. The global proof ingredients follow.

**New uniform geometric theorem:** the
[corner-chain quotient](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-interval-graph-of-corner-chains).
Contract all maximal-corner chains and retain a separate copy for each
normal edge of the full anchor A*. Each unordered chain pair has at most
ONE auxiliary short-edge path; its ceil(length/2) alternating positions
are the parallel copies. The underlying simple graph is an interval graph:
chain B has interval [min(B),R(max(B))], where R(v) is its last natural
right neighbor. Every quotient clique has an original natural-clique
witness. No-articulation natural graphs retain that property (the quotient
may have just two vertices). This is a connectivity model, NOT a K/E
identity for contracted graphs.

An anchor is connected iff its selected quotient multigraph is connected.
A spanning tree followed by arbitrary extra copies therefore constructs a
connected all-cover anchor in EVERY layer n-1 <= k <= m*. This proves
existence, not uniqueness of its original whole component.

**New uniform actual-path theorem:**
[parallel copies of a quotient cover](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#rearranging-parallel-copies-of-a-quotient-cover).
Suppose a selected chain pair B->D has no selected route through another
chain. Every selected normal copy of this pair covers in the original
anchor. Consecutive copy positions have ab->bc->cd with ac,bd maximal
corners. The replacement ab->cd is the actual path

    ab->bc [ac], bc->cd [bd].

At the intermediate state a bypass of bd would give a bypass of cd at
the final anchor, which is impossible. Neighboring occupied/vacant swaps
therefore rearrange ALL selected copies in this class, with arbitrary
exterior, retaining every original strict edge. They can be normalized
to the last m positions by a finite inversion-decreasing procedure.
Quotient support and occupancy counts stay fixed. The result applies to
NN and DN equally.

**New quotient-fork lift:** if r->s and r->t are selected quotient
covers, r<s<t, prepare their last copies rb,rc with a common tail r.
For b<c, flip rb->bc [rc]. For c<b, flip rc->cb [rb], then
cb->bh [ch], where h is c's corner successor. The intermediate corners
cover because a new bypass would imply an old selected s-to-t route,
contradicting the r->t cover. Each move transfers a normal edge from
tail-chain r to tail-chain s, so the sum of tail-chain labels strictly
increases and is bounded. At termination the quotient has at most one
outgoing cover per vertex. Prepare these covers' last copies; every
original vertex then reaches its weak block's greatest vertex while
all maximal corners still cover. This extends the parallel-copy result
to an actual global normalization, without asserting confluence.

**Verification:** `--anchor-quotient-scan` checks all 2055 ordinary diagrams
on 1..8 vertices, using maintained Graph contraction independently of the
interval construction: 6733 corners, 8788 chains, 7783 anchor slots,
3232 quotient triangle witnesses, and 2790 connected all-cover layer
witnesses across 626 connected diagrams. All 196 applicable diagrams
pass the no-articulation assertion. No source-component search occurs.
`--anchor-parallel-slides` checks 1806 anchors in 14 NN/DN fixtures,
5311 quotient covers, 6316 original covers, 1704 adjacent-copy exchanges
and 2320 normalization flips. `--anchor-fork-normalization` independently
normalizes all 1806 anchors, using 967 forks (891 direct and 76 reversed)
and 3367 actual flips including preparation. It verifies 2383 weak blocks'
reachability with the maintained Graph/Poset APIs; the longest path has
11 flips. All three final modes exited zero with empty stderr.
No Lean build or basis/coloring calculation was run.

Frozen sources, exact commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/corner-chain-quotient-20260930/`.
The source model's 21-edge enumeration guard and 20000-component cap are
unchanged. The diagram-only scan does not enumerate states; the parallel
mode returns before complete-component enumeration, with at most 1024
anchors in its largest fixed fixture.

## Remaining general obligation

General NN/DN whole-component collection is STILL UNPROVED. The interval
graph description does not turn graph exchanges into actual flips for free.
The two new theorems supply neither arbitrary-anchor connectivity nor a
replacement for the sum over an original component.

The next path issue is comparing the final one-sink representatives,
including parallel pairs with a selected intervening chain route and
transfers beyond the proved quotient forks. The old six-vertex
cube obstruction is a precise guide: M={03,14,25}, normals
{01,02,12,34,45}, pair 3->5 with route 3->4->5. The edge 02 is redundant
through 01,12, so its direct two-flip slide cannot start. The proved
six-flip cube detour nevertheless exchanges 02 and 35 while corner 14
is redundant in all five intermediate states. Generalize this mechanism,
or repair the actual RHS coefficient boundaries directly. Do not treat
this already-solved component as a new open finite recurrence.

The tested earlier generator set is incomplete even in some solved cases.
Its failures in the 84-state complete-graph, 16-state empty-corner NN and
121-state DN examples are generator limitations, NOT failed component
recurrences. The 125-state area 012333 and 3381-state area 0123434 cases
are also solved. Do not repeatedly re-enumerate them as new obstructions.
General anchor connectivity is one sufficient route, not a requirement:
the requested direct RHS diamonds and endpoint maps remain available.
Never subtract an extra whole source component without its independent
smaller expression.

## Established reductions and checkpoints

- [Outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md) and
  [notebook map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md): four recurrences,
  paired diamonds and endpoint maps; DD/ND inheritance and first-drop
  induction order are proved. NN/DN general collection remains open.
- [Fixed-short reduction](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction):
  all fixed-q and fixed-r components reduce, including incoming DN exterior.
  The unreduced general case has both short edges varying.
- [No joint selection](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#pairing-the-middle-states-when-joint-selection-is-absent):
  exact-exterior middle pairing is proved. It is not a general collection
  theorem; all 66 previously tested examples already reduce independently.
- [Arbitrary source trees](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#full-layer-recurrence-for-arbitrary-source-trees):
  full-layer completion with smaller weak-block and missing-corner corrections.
- [Endpoint attachments](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit):
  proved when the component recurrence preserves the endpoint marks.
  The 84-state NN and coupled 69/126-state examples have their stated
  completed recurrences and attachment extensions.
- [DN via empty-corner NN](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram):
  uniform eligible NN collection would settle DN; do not induct on the
  larger auxiliary NN source.
- [Maximum common-cover layer](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously):
  arbitrary-diagram recurrence at m* and reductions above it are proved.
- [Ordered chain preparation](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners):
  every all-cover state reaches an anchor by actual flips, allowing temporary
  redundant corners. Preparation is not constant on a whole component.
- [Cube-family recurrences](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-component-recurrences-for-cubes-of-paths-on-3h-vertices):
  all layers for cubes on 3h vertices, proved uniformly in h; checkpoint
  `89f3e6e`, recorded at `941e6dd`. The 125-state example is included.
- [Outer-cover path](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#triangle-exchange-with-a-covering-outer-edge)
  and [unequal-chain finite certificate](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#a-checked-whole-component-recurrence-with-unequal-chains):
  proof checkpoint `4c76d99`, recorded at `f7c42d6`. All layers of area
  0123434 with 04,26 strict are complete, including the 3381-state case.
  Neither result asserts arbitrary-diagram component uniqueness.

## Ownership, restrictions and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, earlier authorized endpoint/source-addition continuations, handoff
archives, and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve all other ownership and both proof-note prefixes at `f7c42d6`.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Any later authorized Lean work stays serialized under the primary owner.
No worker/account/profile/model assignment changed. Runtime registry,
`codex mcp list`, Rust guide, current Cargo metadata and existing Graph,
Poset and flip APIs were checked. Lean MCP is rooted at RealRooted and unused.
Maintained Rust stays clean at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.

The original replacement began at pushed account-swap `2511182`.
The complete handoff at `f7c42d6`, including receipts and prior ownership,
is preserved in the
[pre-chain-quotient archive](docs/archive/component-handoff-before-chain-quotient-20260930.md).
Only relative Markdown links were relocated. All earlier proof-note text
is an unchanged prefix. No background job needs monitoring or restarting.

Both proof-note prefixes, the relocated archive, all 154 local file links,
receipt hashes and `git diff --check` pass before checkpointing.

Proof checkpoint `70d106e` is pushed to `origin/main`. All three diagnostic
jobs are complete; no process needs monitoring or restarting.

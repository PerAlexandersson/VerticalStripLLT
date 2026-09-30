# VerticalStripLLT handoff

## Current continuation — all layers in the cube family

Primary resumed from clean pushed `21e9814`. The previous goal turn and
this continuation made verified progress; the FULL goal remains active:
prove the ordinary non-circular component expansion by the author's four
diagram recurrences. The completed Lean word-functional theorem is NOT
an input. The user excludes fundamental-basis calculations. Keep whole
components, diamonds and actual flips central.

**New proved uniform family:**
[complete cube-family recurrences](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-component-recurrences-for-cubes-of-paths-on-3h-vertices)
and their [DN version](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#all-dn-layers-for-cubes-of-paths-on-3h-vertices).
For the natural graph G_n with edges of lengths 1,2,3 on n=3h>=6
vertices, the maximal corners are the three residue-class chains.
Every simultaneous-cover state normalizes to an anchor whose normals
lie in h disjoint triangles. The proof now connects ALL anchors with
the same edge count and weak-component partition, for arbitrary h.

The local proof uses only two adjacent triangles. All three edge types
can be moved between the triangles; the nonconsecutive type uses the
six-flip path with temporary redundant corners. A four-flip path
{01,12}->{01,02}, retaining 03,13,03,03, together with the normal-long
triangle flip and order reflection, changes any two-edge triangle to
any other. Row rearrangements and these exchanges connect the three
row-count vectors. The same local moves connect arbitrary numbers of
triangle blocks; outside vertices cannot affect their interval cover tests.

Hence at EVERY k=n-1,...,2n-3 there is one connected component C_k
selecting all maximal corners with a simultaneous-cover witness.
Every other component independently reduces by absent-corner deletion,
weak-block reordering, or alternating corner deletion. Full-layer
subtraction now gives complete NN/DN component recurrences in all these
layers. Components outside this range reduce too. This is an induction
step in whole smaller diagrams, not an appeal to their known expansion.

The formerly open 125-state eight-edge NN example in area 012333 is
solved. Its two target layers contain 23 components / 210 states;
13 absent-corner corrections account for 84 states and one alternating
singleton accounts for one: 125=210-84-1. For n>=9 the native DN contact
is u=n-7,w=n-4,x=n-3,z=n-1, with upper corner (n-6)(n-3) unmarked.
For n=6 use NN at w=2,x=3,z=5 with 03 unmarked.

**Verified, graph-only:** 80 explicit local template instances / 236
actual flips; 822 ordered pairs in the six-vertex local path table.
The global row algorithm passes ALL anchors for h=2,3,4 (4672 states)
and 582 bounded samples for h=5,6, replaying 143893 actual flips in
full graphs on up to 18 vertices. Local BFS supplies a fixed six-vertex
lookup table; there is no global path search. The written proof uses
the explicit local templates, not enumeration as an unbounded argument.
All 13 connected-support layers for n=6 and n=9 have verified complete
corrections: 28158 survivor states, 181 absent-corner corrections /
31162 states, 18 whole reordered-block corrections / 90 states, and
14 alternating corrections / 16 states (546 whole deletion terms).
Every final diagram decreases the original order. The two principal
runs and the final one-hole/max-layer regression checks exited zero with
empty stderr; no Lean build was run.

Frozen source, commands and logs:
`/lake-cache/ai-projects/requests/VerticalStripLLT/cube-component-recurrences-20260930/`.
The general 21-edge enumeration guard and 20000-component cap are
unchanged. Larger n=12,15,18 checks replay bounded prescribed paths only;
they DO NOT enumerate those global state spaces.

## Remaining general obligation

General NN/DN whole-component collection remains unproved outside the
established families. The cube theorem uses three equal corner chains
and disjoint triangle blocks. Arbitrary diagrams have different chain
lengths and more interacting chains; the two-block proof has not been
extended to that geometry. Do not claim that all simultaneous-cover
states at one edge count always lie in one component.

The 3381-state eight-edge component in area 0123434 remains outside
this family. Its corners 04,26 give two length-two chains and three
singletons. The new general anchor observation reduces its witnesses
to subsets of the fixed alternating state, but does not yet connect or
collect them. Continue with the local flip templates and their cover
conditions in this more general geometry. Keep direct RHS repairs
available; source completion is only one sufficient method.

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

- [Maximum simultaneous-corner layer](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously):
  proved for arbitrary diagrams, using short-edge paths and the rightmost
  priority. The one-corner dense-layer theorem also remains valid.
- [General corner-chain preparation](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners):
  every simultaneous-cover state reaches an explicit mixed-acyclic anchor,
  allowing temporarily redundant other corners. The endpoint is not constant
  on a whole component. The six-vertex obstruction to all-cover paths remains
  valid, although its whole component recurrence is now solved above.

## Ownership, restrictions and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, earlier authorized endpoint/source-addition continuations, handoff
archives, and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve all other file ownership and both proof-note prefixes at `21e9814`.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Any later authorized Lean work remains serialized under the primary owner.
No worker/account/profile/model assignment changed. Runtime registry,
`codex mcp list`, Rust guide, Cargo metadata and existing Graph/Poset/flip
APIs were checked this turn. Lean MCP is rooted at RealRooted and unused.
Maintained Rust remains clean at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.

The user-requested replacement began at pushed account-swap `2511182`.
The complete handoff at `21e9814`, including prior results, exact proof
checkpoints, receipts and ownership, is preserved in the
[pre-cube archive](docs/archive/component-handoff-before-cube-family-20260930.md).
Only relative Markdown links were adjusted. It links the older account-swap
and pre-dense archives. Earlier proved/unfinished distinctions are retained;
the new appendices explicitly supersede only the cube-family open cases.

Both proof-note prefixes, the complete archived handoff, all 140 local file
links in the five edited/new files, receipt hashes and `git diff --check` pass. The worktree
was clean and HEAD/origin/main agreed at the start. No job needs restarting.

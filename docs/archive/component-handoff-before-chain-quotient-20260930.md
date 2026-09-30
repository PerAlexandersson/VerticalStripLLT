# VerticalStripLLT handoff

## Current continuation — general cover criterion and unequal-chain certificate

Primary resumed from clean pushed `941e6dd`. The previous goal turn and
this continuation made verified progress. The FULL goal remains active:
prove the ordinary non-circular component expansion by the author's four
diagram recurrences. Do NOT use the completed Lean word-functional theorem
or fundamental-basis calculations. Whole components, diamonds and actual
flip paths remain the requested approach.

**New uniform path theorem:**
[triangle exchange with a covering outer edge](../proofs/COMPONENT_NN_REDISTRIBUTION.md#triangle-exchange-with-a-covering-outer-edge).
For a<b<c<h, A selecting ah,ab,bc and omitting ac connects to B=A-bc+ac
by ab->bh [ah], bc->ch [bh], bh->ab [ah], ch->ac [ah], EXACTLY when
ah,ab cover in A and ac covers in B. The cover of bc follows from these.
The dual uses an incoming outer dc. The outer edge can be normal and
nonmaximal; no anchor assumption is needed. All strict edges are retained.
This proves component membership, NOT equality of state valuations.

**New completed finite NN case:**
[all layers of area 0123434](../proofs/COMPONENT_NN_REDISTRIBUTION.md#a-checked-whole-component-recurrence-with-unequal-chains).
Its corners are 04,26, with two two-vertex chains and three singletons.
The full anchor has normals {02,12,13,14,34,35,36,45,46,56}.
Actual local flips, guarded triangle moves and paths P(U)->U->V->P(V)
for all-cover flip neighbors U,V give explicit spanning trees connecting
ALL connected anchors in each layer k=6,...,12. The projection paths
are the already proved ordered corner-chain normalization.

The independent certificate verifier enumerates just the 1024 anchor
subsets, derives the expected connected sets, and replays all tree edges.
It does NOT search whole source flip components: 674 anchors, 667 tree
edges, 2306 actual flips. Therefore each layer has one connected component
with a simultaneous-cover witness. Every other component independently
reduces by weak-block reordering or alternating corner deletion. The full
NN layer identity gives the requested whole-component recurrence.

The formerly open 3381-state eight-edge component is now solved. Its
root anchor is {02,04,12,13,14,26,34,35}. There are 162 actual target
components / 5005 states, 74 whole block corrections / 1039 states,
and 16 alternating source corrections / 585 states, giving 180 whole
deletion terms. Thus 3381=5005-1039-585; the common K/E coefficients
come from the diagram identities, not from this count check.

**Verified:** the endpoint-cover criterion passes 157728 configurations
in 14 NN/DN fixtures, including 33498 four-flip paths, of which 4128
retain a nonmaximal normal outer edge. All seven NN recurrences above
have verified whole corrections: 21577 survivor states, 415 reordered
block components / 4236 states, and 553 alternating source components
/ 4438 states, yielding 2167 whole deletion terms. The independent
anchor certificate replay also passes. All three final modes exited
zero with empty stderr. No Lean build was run.

Frozen source, certificate, commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/unequal-chain-anchor-recurrences-20260930/`.
The certificate is `anchor-certificate.txt`; masks use the sorted natural
edge list for area 0123434. The standalone replay mode is
`--verify-anchor-certificate`; it reads the task-owned /tmp copy named
in the receipt. The 21-edge enumeration guard and 20000-component cap
are unchanged. All existing larger cube checks remain bounded path replays.

## Remaining general obligation

General NN/DN whole-component collection is STILL UNPROVED. This turn's
outer-cover path is uniform, but the spanning-tree certificate is finite
and specific to area 0123434. Do not infer arbitrary-diagram uniqueness
of the component containing common-cover states.

The tested generator set is not complete in general. Even after adding
projected all-cover flips, it splits the 84-state complete-graph case,
a 16-state empty-corner NN case and a 121-state DN case. These are gaps
in this generator approach, NOT failed component recurrences: the 84-state
component already has an independent completed signed recurrence. Do not
spend another turn rediscovering that example's recurrence, or treating
012333 / 0123434 as still-open component cases.

The unresolved step is handling arbitrary paths through redundant-corner
states, or directly repairing the RHS coefficient boundaries. The new
four-flip theorem needs actual endpoint covers; the projected-flip generator
needs both raw endpoints to cover all corners. Neither covers every such
boundary. General anchor connectivity is only one possible sufficient
route; keep direct RHS diamonds and endpoint maps available. Do not add
unreduced whole source components and then subtract them by assumption.

## Established reductions to retain

- [Outline](../proofs/COMPONENT_RECURRENCE_OUTLINE.md) and
  [notebook map](../proofs/COMPONENT_NOTEBOOK_MAP.md): the four recurrences,
  paired middle diamonds, identity sectors and whole-exterior endpoint maps.
  DD/ND inheritance and the first-drop induction order are proved.
- [Fixed terminal short](../proofs/COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction):
  all fixed-r components reduce, including arbitrary incoming DN exterior.
  Fixed-q cases are proved too. The remaining general case has both varying.
- [No joint short selection](../proofs/COMPONENT_NN_REDISTRIBUTION.md#pairing-the-middle-states-when-joint-selection-is-absent):
  every 01 state has both arms as bridges and its exact-exterior 10 mate.
  This is one-way pairing, not a full recurrence for that class. All 66
  tested examples already reduce by blocks, smaller envelope, trees or
  inactive corners; their seven raw-image boundaries are not new open cases.
- [Arbitrary source trees](../proofs/COMPONENT_NN_REDISTRIBUTION.md#full-layer-recurrence-for-arbitrary-source-trees):
  complete NN/DN recurrences, including unsaturated sources. Extra source
  layer components either delete a missing corner or become one whole
  smaller component by concatenating their induced weak-block diagrams.
- [Endpoint attachments](../proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit):
  proved for endpoint-preserving recurrences. The earlier 84-state NN and
  coupled 69/126-state examples also have completed recurrences and their
  stated attachment extensions. They do not settle arbitrary crossings.
- [DN through an empty corner](../proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram):
  a general eligible NN collection theorem, allowing empty unmarked corners,
  would settle DN. Do not induct on the larger auxiliary NN source itself.

- [Maximum simultaneous-corner layer](../proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously):
  proved for arbitrary diagrams, using short-edge paths and the rightmost
  priority. The one-corner dense-layer theorem also remains valid.
- [General corner-chain preparation](../proofs/COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners):
  every simultaneous-cover state reaches an explicit mixed-acyclic anchor,
  allowing temporarily redundant other corners. The endpoint is not constant
  on a whole component. The six-vertex obstruction to all-cover paths remains
  valid, although its whole component recurrence is solved by the cube-family
  theorem below.

- [Cube-family recurrences](../proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-component-recurrences-for-cubes-of-paths-on-3h-vertices):
  ALL layers are proved for natural cubes of paths on n=3h>=6 vertices.
  The proof uses explicit six-vertex moves and three-row rearrangements.
  This is uniform in h; the new unequal-chain result above is a separate
  finite certificate. Receipt: `cube-component-recurrences-20260930/`.

## Ownership, restrictions and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, earlier authorized endpoint/source-addition continuations, handoff
archives, and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve all other ownership and both proof-note prefixes at `941e6dd`.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Any later authorized Lean work remains serialized under the primary owner.
No worker/account/profile/model assignment changed. Runtime registry,
`codex mcp list`, current Rust metadata and existing Graph/Poset/flip APIs
were checked; the Rust guide was already read in this continuation chain.
Lean MCP is rooted at RealRooted and unused. Maintained Rust stays clean
at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.

The user-requested replacement began at pushed account-swap `2511182`.
The complete handoff at `941e6dd`, with prior proof checkpoints, receipts
and ownership, is retained in the
[pre-unequal-chain archive](component-handoff-before-unequal-chain-20260930.md).
Only relative Markdown links were adjusted. It links the previous cube,
account-swap and pre-dense history. Earlier proof-note text remains an
unchanged prefix; only the new appendices supersede the seven-vertex gap.

Both proof-note prefixes, the archived handoff, all 145 local file links,
receipt hashes and `git diff --check` pass. The frozen-source certificate
replay also exited zero and reproduced all 2306 checked flips. The checkout was
clean and HEAD/origin/main agreed at the start. No job needs restarting.

Proof checkpoint `4c76d99` is pushed to `origin/main`. All diagnostic jobs
are complete; no background process needs monitoring or restarting.

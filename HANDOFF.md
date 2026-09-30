# VerticalStripLLT handoff

## Current continuation — unrestricted slides and three-chain recurrences

Primary resumed from clean pushed `c2078e6`. The previous goal turn made
verified progress; this continuation proves a new uniform transport and
complete component recurrences for an unbounded class. The FULL goal is
still active: finish the author's general NN/DN whole-component argument
for ordinary non-circular paths. Do NOT substitute the completed Lean
word-functional proof or fundamental-basis calculations.

**New unrestricted path theorem:**
[sweep and restore](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#sweep-aside-the-obstructions-and-restore-them-after-the-slide).
For a<b<c<d, suppose A selects ac,bd,ab, omits cd, and ac,bd cover.
The retained longs may be normal. Move every selected av with a<v<b
across ac, in increasing v; move every selected vd with c<v<d across
bd, in decreasing v. Then ab->bc [ac], bc->cd [bd]. Undo the first
sweep in reverse order and then the second. Every flip is actual and
the exact endpoint is A-ab+cd. The net core change lies outside the
intervals testing the shorts during restoration. Path length is
2+2|L|+2|R|. Every original strict edge stays selected.

This finally removes the old short-cover/quotient-cover restriction.
Other corners may become redundant temporarily. The six-flip cube
obstruction is exactly the L={1},R={4} instance, not a new open case.

**New canonical packing:**
[every parallel class](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#pack-every-parallel-class-including-noncovers).
Adjacent occupied/vacant copies now exchange in ANY chain pair. All
anchors with fixed occupancy counts m_e belong to one original component
and reach the single packed anchor selecting the last m_e copies in
each class. Its terminal reachability is exactly the quotient's, and
its HRV map is h(v)=h_H(r(v)). This is a representative statement,
NOT a replacement of a whole component sum by one state's valuation.
The remaining general comparison is between DIFFERENT occupancy vectors.

**New complete whole-component recurrences:**
[three chains without articulation](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-recurrences-for-three-corner-chains-without-articulation).
Every connected natural graph with three corner chains and no articulation
is exactly the square of a path plus the edges i(i+3) for one nonempty
consecutive interval p<=i<=q. A 4-, 5-, or 6-vertex cube window contains
a good copy of every chain pair. The only new small window lemma uses
ten written actual flips connecting four anchors in cube P5's middle
layer. The other local layers use proved tree, maximum and cube P6 paths.

Unrestricted packing brings a selected donor, vacant receiver and selected
third buffer class into that window. The local connected common-cover
path transfers one unit between classes. If the third class is absent,
use i->l, i->j, l->i. All connected occupancy vectors of a given total
therefore connect, for arbitrary capacities. Thus each feasible layer
has exactly ONE connected component with a common-cover witness.
Every other source component independently reduces by missing corners,
weak blocks or alternating deletion. Full NN/DN layer subtraction gives
complete signed recurrences in smaller WHOLE components. This proves
all layers, including unmarked maximal-corner sectors, uniformly in n,p,q.
It includes cubes of every length, not only n=3h, and square-path tails.
Two corner chains need only packing, so the same isolation works there
without a no-articulation assumption.

## Verification and receipt

All four final graph-only modes exited zero with empty stderr:

- `--crossing-cover-slides`: 89252 explicit paths / 228604 actual flips
  in 14 fixtures; 57374 paths have a nonmaximal retained long. Of 6766
  paths with all-cover endpoints, 1943 pass through a redundant corner.
- `--anchor-packet-packing`: 1806 anchors, 1017 occupancy packets,
  1527 slides / 3970 flips, including 367 noncover-class slides and
  231 redundant excursions. Maintained Poset checks exact HRV maps.
- `--three-chain-window`: all 165 parameter choices on 4..12 vertices;
  4913 occupancy packets, 12996 transfers / 240283 actual flips,
  1030 connected layers. Maximum path length 63. Only the fixed local
  windows use state lookup, on at most six vertices / 512 states.
- `--three-chain-layer-recurrences`: 15 complete source layers for NN
  area 0122322 and DN cubes on seven and eight vertices. Totals:
  7378 survivor states; 237 target components / 16448 states;
  23 reordered-block corrections / 89 states; 161 absent-corner
  corrections / 8966 states; 5 alternating source corrections /
  15 states, yielding 139 whole deletion terms. Both directions of
  block-image flip graphs and all smaller-diagram conditions pass.

Frozen source, commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/crossing-slides-three-chains-20260930/`.
No Lean build, worker, maintained Rust edit, basis calculation or coloring
calculation was run. The 21-edge enumeration guard and 20000-component
cap remain. The n<=12 source-path audit may inspect 30 natural edges but
NEVER searches their global state space; only local window search is used.
The separate fixed whole-layer checks stay within 18 natural edges.

## Remaining general obligation

General NN/DN whole-component collection is STILL UNPROVED. Packing
within each occupancy vector is now complete, even for noncover pairs.
Do not reopen that obstruction. The new family theorem isolates all
connected common-cover states only for two chains, or for three chains
without articulation. More general transfers between different occupancy
vectors still need actual paths or a direct RHS component repair.
Multi-block three-chain cases also require their own reductions unless
already covered by a proved endpoint-preserving recurrence.

A useful next core is an arbitrary complete natural graph with its one
maximal corner: its anchor classes each have capacity one, so packing
alone cannot address the remaining transfers. The fixed K5/84-state
recurrence is already solved; seek a uniform argument, not another audit
of that example. More generally, a window containing additional chain
vertices does not inherit the three-chain cover tests automatically.

The family theorem is an induction step in smaller diagrams; these need
not stay in the family. Do not equate it with the full e-expansion proof,
assume general active-component uniqueness, or subtract an unresolved
extra source component. Direct RHS diamonds and endpoint maps remain
allowed alternatives to source-component isolation.

## Established results to retain

- [Recurrence outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md) and
  [notebook map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md): DD/ND inheritance,
  first-drop induction, paired diamonds and exact endpoint maps are proved.
- [Fixed-short reductions](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction):
  all fixed-q and fixed-r components reduce, including incoming DN exterior.
- [Endpoint attachments](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit):
  completed for endpoint-preserving recurrences. The 84-state and coupled
  69/126-state examples retain their proved attachment extensions.
- [DN through empty-corner NN](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram):
  a uniform eligible NN collection theorem would settle DN; do not induct
  on the larger auxiliary source itself.
- [Tree layers](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#full-layer-recurrence-for-arbitrary-source-trees)
  and [maximum common-cover layers](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously):
  complete whole-component recurrences with arbitrary exterior.
- [Corner-chain preparation](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners)
  and [fork normalization](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#lifting-a-quotient-fork-and-obtaining-one-sink-in-each-block):
  actual paths from common-cover states to anchors, then to all-cover states
  with one sink per weak block. Packing now gives canonical representatives
  per occupancy vector; distinct vectors can still lie in one component.
- [Interval quotient](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#the-interval-graph-of-corner-chains):
  one short-edge path per chain pair, exact interval and clique geometry;
  proof checkpoint `70d106e`, recorded at `c2078e6`.
- The cube-family theorem (`89f3e6e`) and unequal-chain finite certificate
  (`4c76d99`) remain proved. The 125-state area 012333 and 3381-state
  area 0123434 examples are NOT open. The latter has more than three
  chains and is not subsumed by the new unbounded family.

## Ownership, restrictions and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, earlier authorized endpoint/source-addition continuations, handoff
archives, and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and both proof-note prefixes at `c2078e6`.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Any later authorized Lean work stays serialized under the primary owner.
Runtime registry, `codex mcp list`, current Cargo metadata and existing
Graph/Poset/flip APIs were checked. The Rust guide was already read in
this continuation chain. Lean MCP is rooted at RealRooted and unused.
Maintained Rust stays clean at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
No worker/account/profile/model assignment changed.

The replacement originally began at pushed account-swap `2511182`.
The complete handoff at `c2078e6`, including earlier receipts and ownership,
is preserved in the
[pre-unrestricted-slide archive](docs/archive/component-handoff-before-unrestricted-slides-20260930.md).
Only relative Markdown links were relocated. Earlier proof-note text
remains an unchanged prefix. All diagnostic jobs are complete.

Both proof-note prefixes, the relocated archive, all 159 local file links,
receipt hashes and `git diff --check` pass before checkpointing.

Proof checkpoint `c18115d` is pushed to `origin/main`. All four diagnostic
jobs are complete; no process needs monitoring or restarting.

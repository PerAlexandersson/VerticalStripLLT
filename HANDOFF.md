# VerticalStripLLT handoff

## Current continuation — complete-diagram component induction

Primary resumed from clean pushed `1498536`. This continuation made verified
progress: it proves all complete-diagram NN component recurrences, uniformly
in the number of vertices and the selected edge count. The FULL goal remains
active and UNFINISHED: general ordinary NN/DN whole-component collection.
Use the author/Robin diagram method. Do not substitute the separate completed
Lean word proof, a fundamental basis, or a representative's point valuation.

**New theorem:** [complete-diagram induction](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-diagrams-every-connected-active-layer-is-one-component).
On vertices 0,...,n, with complete natural graph and outer corner f=0n,
all connected k-edge states where f covers lie in one actual component C_k,
for n<=k<=1+binom(n,2). Every connected component active at f is one of these.

The proof is entirely by actual flips:

1. Previous preparation gives an anchor f+H on internal vertices 1,...,n.
   Remove outgoing cover forks to obtain an ancestor tree. Merge children
   i<j of n by in->0i [0n], jn->0j [0n], 0i->ij [0j], 0j->jn [0n].
   Make n-1 the sole child, open (n-1)n to 0(n-1), induct below it, then
   close. This gives the entire internal chain 12,23,...,(n-1)n.
2. Open that chain right to left to expose 0b. Smaller complete-diagram
   paths on {0,a,...,b} lift and the opening can be reversed, with every
   exterior edge restored. This includes nonconsecutive ordered subsets:
   no edge from 0 goes below a, so those omitted vertices cannot interfere.
3. For n>=5, the chord-position sets in [1,n-1] and [2,n] overlap (at 24)
   and together contain every chord except 1n. Induction therefore connects
   every chord set with fixed cardinality and fixed 1n bit.
4. The remaining bit has an explicit bridge. When 1n is absent and 13,2n
   are selected, sweep all incoming edges in to 0i across 0n in decreasing
   i. Flip 12->01 [02], then undo the column sweep in increasing i,
   including new 01. Exact result: A-12+1n. Open the chain down to 3,
   use the four child-merging flips to replace 13 by 12, and close it.
   Exact result: A-13+1n, with arbitrary other chords retained.
5. A lone chord uses a shorter bridge: open down to 2, do 13->01 [03],
   01->1n [0n], then close. Counts zero/full are trivial. Four explicit
   five-vertex paths in the proof give the induction base.

Thus the whole NN recurrence for C_k is the full target layers k and k-1,
minus independently smaller expressions for all other source components.
Those extras are disconnected (weak-block reordering) or inactive at f
(corner deletion). Higher/lower layers reduce directly. Every final term is
WHOLE and smaller. Correction diagrams need not themselves be complete:
this is an induction step, not a proof of the full general expansion.

## Verification and receipt

Both graph-only modes passed with exit zero and empty stderr:

- `--complete-chain-induction`: 28192 connected-anchor normalizations /
  722498 actual flips; 1617 chord-comparison paths / 1057322 actual flips.
  Maximum path lengths 95 and 8363. All anchors and chord subsets are
  exhausted through seven vertices; deterministic bounded samples and every
  chord density are tested through ten vertices. Only the fixed base on at
  most five vertices searches components (at most 512 states). The general
  construction searches the chord-position graph, not source components.
- `--complete-corner-layers`: 14 complete NN source layers on three through
  six vertices. 10432 survivor states; 1442 whole target components / 15886
  states; 406 block corrections / 1688 states; 860 inactive-corner
  corrections / 3766 states. These give 1442 positive and 1266 negative
  whole terms; all smaller-diagram and both-direction block checks pass.

Frozen sources, exact commands, logs, verification and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/complete-corner-induction-20260930/`.
The existing external consumer and maintained Graph/Poset APIs are reused;
no maintained Rust or Lean source was edited. No Lean build, worker, basis
calculation or coloring calculation ran. Existing full-enumeration guards
(21 natural edges and 20000-state components) remain unchanged. Larger
complete graphs, through 45 natural edges, use only explicit paths.

## Remaining general obligation

General NN/DN whole-component collection remains UNPROVED. A complete
natural graph has only one maximal corner; the new NN result does not
settle arbitrary DN through the conditional empty-corner construction.
The [DN continuation](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#what-the-complete-diagram-induction-supplies-for-dn)
records the exact usable local consequence and the missing hypothesis.

Every maximal-corner interval in an arbitrary ordinary diagram is a clique.
If its selected restriction is connected and that corner covers, the new
paths compare all such restrictions of fixed edge count, fixing all exterior
edges and original strict corners. Forward cover tests cannot leave that
contiguous interval and return. This is a possible next approach to general
occupancy transfers. But global connectedness does NOT ensure connectedness
of each selected interval restriction. Establish the needed preparation or
handle the disconnected local blocks; do not assume it automatically.

Canonical packing WITHIN every occupancy vector is already proved, including
noncover classes. Transfers BETWEEN vectors are now settled for two chains,
three chains without articulation, and complete natural graphs. Do not
reopen these solved cases. Arbitrary overlapping corners and multi-block
cases outside proved endpoint-preserving extensions still need work.
Direct RHS diamond repairs and valid endpoint maps remain alternatives.

## Established results to retain

- [Recurrence outline](docs/proofs/COMPONENT_RECURRENCE_OUTLINE.md) and
  [notebook map](docs/proofs/COMPONENT_NOTEBOOK_MAP.md): DD/ND inheritance,
  first-drop induction, paired diamonds and exact endpoint maps are proved.
- [Fixed-short reductions](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction):
  all fixed-q/fixed-r components reduce, including incoming DN exterior.
- [Endpoint attachments](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit):
  completed for endpoint-preserving recurrences only. Do not automatically
  attach arbitrary full-layer corrections which relabel an endpoint.
- [Unrestricted crossing slides](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#sweep-aside-the-obstructions-and-restore-them-after-the-slide)
  and [canonical packing](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#pack-every-parallel-class-including-noncovers):
  fixed occupancy vectors are fully connected, with explicit actual paths.
- [Three-chain recurrences](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-recurrences-for-three-corner-chains-without-articulation):
  all eligible NN/DN layers for the square of a path plus a nonempty interval
  of length-three edges. This is exactly the connected three-corner-chain
  family without articulation. Two chains need packing alone.
- Arbitrary tree recurrences, maximum common-cover layers, corner-chain
  preparation, interval quotient and fork normalization remain proved.
- The 84-state K5, coupled 69/126 examples, 125-state area 012333,
  3381-state area 0123434 and cube families are solved. The new theorem
  subsumes complete-source NN layers, not the distinct DN exterior cases.

## Ownership and recovery

The replacement primary owns this handoff, the recurrence outline,
APPEND-ONLY continuations of the NN redistribution and DN joint-repair
notes, earlier authorized endpoint/source-addition continuations, handoff
archives, and the existing external diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and both proof-note prefixes at `1498536`.

No Lean/Lake builds, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit, or maintained Rust edit is authorized in this lane.
Any later authorized Lean work stays serialized under the primary owner.
Runtime registry and `codex mcp list` were checked; current Cargo metadata
and existing Graph/Poset/actual-flip APIs were inspected. The Rust guide was
already read in this continuation chain. Lean MCP is rooted at RealRooted
and unused. Maintained Rust stays clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`.
No worker/account/profile/model assignment changed.

The replacement originally began at pushed account-swap `2511182`.
The full handoff at `1498536` is preserved in the
[pre-complete-corner archive](docs/archive/component-handoff-before-complete-corner-20260930.md),
with only relative Markdown links relocated. It retains the prior proof
checkpoint `c18115d`, verification receipts and links to earlier ownership.
Both proof-note prefixes remain unchanged. All diagnostic jobs are complete;
there is no running process or blocked external dependency.

Both proof-note prefixes, the exact relocated archive, 155 local file links,
final frozen-source replays, receipt hashes and `git diff --check` pass.

Proof checkpoint `4ca99c3` is pushed to `origin/main`. Both diagnostic jobs
are complete; the full general NN/DN goal remains active, with no external
blocker or running process.

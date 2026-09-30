# VerticalStripLLT handoff

## Current continuation — last-clique inheritance and the full 0a,bc,ae family

Primary resumed from clean pushed `28bc4b9`. The previous turn and this
continuation made verified progress. The full general NN/DN goal remains
ACTIVE and UNFINISHED. Continue the author/Robin diagram method: whole
components, diamonds and justified relabeling. No fundamental basis or
substitution of the separate completed Lean proof.

**New proved inheritance theorem:** if the last two maximal corners of
an ordinary graph are bc,ae with b<a<c<e, common-cover uniqueness in the
induced core V={0,...,c} union {e} implies it in the full graph. Earlier
corners are arbitrary. See [the complete path proof](../proofs/COMPONENT_NN_REDISTRIBUTION.md#extending-the-last-clique-from-a-connected-core).
This hypothesis must be proved for the core; do not silently assume it.

**New proved family:** [all middle positions](../proofs/COMPONENT_DN_JOINT_REPAIRS.md#all-positions-of-the-middle-corner-in-0abcae)

    M={0a,bc,ae},       0<b<a<c<e.

This removes the remaining b=1 or c=e-1 restrictions. In the compressed
core the last two heads are consecutive, and the last-vertex chain starts
at 0. Reverse pendant preparation, delete that pendant, and use the proved
two-overlapping-clique theorem. The new inheritance theorem then gives
common-cover uniqueness in the full source, in every feasible layer.
Independent corrections and full-layer subtraction give each eligible
whole-component recurrence, with identical signs for K and E. Right-marked
identities and arbitrary right attachments remain valid.

Eligibility matters: for b>1, adding 0(a+1) alone is not an ordinary
natural diagram, since 1(a+1) is absent. The old direct DN contact is NOT
available there. The left NN contact deletes 0a and marks 1a. For b=1,
keep the earlier DN contact and its middle-mark restriction.

### The path argument to retain

1. Prepare an anchor. In its last clique, normalize the block containing
   ae to a terminal star at e. Every other right block meets [a+1,c];
   connect that intersection internally by the earlier reachability
   construction. All endpoints remain anchors. Global connectedness now
   forces the selected core V to be connected.
2. Sweep exterior ve, c<v<e, to av in decreasing v. There is no return
   from the omitted vertices into V, so every core flip lifts. A core
   anchor endpoint lets us undo the sweep in increasing v, restoring
   the exact exterior.
3. Choose a good core spanning tree containing all corners and all ve,
   a<v<=c. Rearrange the core to contain it, then normalize the now
   connected full right clique. This gives a fixed full spanning tree T.
4. Extras inside V rearrange by the core theorem. Extras in the right
   terminal clique, together with ba, rearrange by the proved terminal-
   clique transfer construction: ba,ce are its doubled class, and their
   crossing slide restores arbitrary exterior. The two sets share ba,
   which is outside T. Route exchanges through ba to connect every
   fixed-count selection of extras.

For the three-corner family take

    T=M + {va:1<=v<a,v!=b} + {ve:a<v<e}.

The construction is a path theorem, not a contraction identity for
component values. All whole-output assertions still use independent
absent-corner, weak-block and alternating-deletion corrections.

### A failed shortcut is now excluded by a bound

For b>1, deleting pendant 0 introduces 1a. Its common-cover maximum is
|A*|-1-(a-2), whereas deleting 0 from the full source anchor leaves
|A*|-1 edges. Thus count-preserving activation of every new corner is
impossible at the top layers. For 03,24,36 the figures are 8 versus 7.
This is not a counterexample to the component theorem. Use the connected
core and restored exterior above instead.

Also, sweeping incoming edges at c does not make c pendant: outgoing
cv with v>c can remain. A preliminary bridge experiment caught this;
the corrected diagnostic normalizes the right blocks first.

## Verification and receipt

Frozen receipt directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/three-corner-tail-recurrences-20260930/`.
All four final source-identical replays passed with exit 0 and empty stderr.
Receipt hashes pass; no verification jobs remain running.

- `--three-corner-tail-star`: 45 diagrams on 5..10 vertices, c<=5;
  all connected anchors through seven vertices and 128 deterministic
  subset samples per larger diagram. 3279 constructed paths, 387658
  checked actual flips, maximum path length 725, up to 34 natural edges.
  Counts include 63 overlap joins, 10024 lifted core flips and 128764
  final-clique flips. Every endpoint contains T and is an anchor.
- Only the compressed core uses bounded path search, with at most seven
  vertices, sixteen natural edges and 8192 states. The arbitrary core
  theorem comes from the prior proved path lemmas. The star mode does
  not execute every later extra-edge redistribution; that step reuses
  the proved core and terminal-clique constructions.
- `--three-corner-tail-layers --right-marked-layers`: all 16 feasible
  NN layers in (n,a,b,c)=(7,3,2,4),(8,3,2,4),(8,4,3,5), all corners marked.
  16165 survivor states; 1206 whole targets / 29678 states; 535 block
  corrections / 7182 states; 314 alternating sources / 6331 states,
  yielding 7490 whole deletion terms. 4794 positive and 4437 negative
  terms, 44317 redundancy witnesses. All signed marked fibre identities,
  whole-output assertions and induction-order checks pass.
- Supplementary `--dn-general-bridge`: 126 diagrams on 5..10 vertices,
  2386 shared-class introduction paths, 132032 flips, maximum 644.
- Supplementary `--dn-core-isolation`: smaller core {0,...,a,c,e}, a<=3,
  in 51 diagrams on 5..10 vertices; 3306 paths, 23105 flips, 5345 lifted
  core flips, 1734 changed core endpoints. Exterior restoration is exact.
  These two supplementary modes are not assumptions of the new theorem.

Only the existing external `dn_joint_span.rs` consumer changed. Existing
Graph/Poset, actual-flip, complete-clique and reachability code is reused.
The old six-vertex/512-state helper is preserved as a wrapper; its new
explicitly bounded seven-vertex core caller allows 8192 states, justified
by at most sixteen natural edges with three fixed corners. The existing
20000-state whole-component guard is unchanged. No coloring enumeration,
basis calculation, new polynomial generator or Lean build ran. Python
only orchestrated files, commands and summaries of diagnostic logs.

## Remaining problem

General NN/DN collection remains unproved. The family 0a,bc,ae is now
solved; do not retain its interior-middle cases on the open list.

Other three-corner geometries 0a,bc,de with d!=a, and general higher-clique
sources, still need a proof. The new last-clique inheritance (and its
order-dual path version) removes endpoint extensions only when the smaller
core's uniqueness is available. It does not prove arbitrary core uniqueness.
Direct RHS diamond redistribution remains an alternative to global
common-cover uniqueness. The earlier six-fixture generator experiments
are finite evidence only, not a general generation theorem.

## Earlier results and ownership

The [previous handoff](../archive/component-handoff-before-tail-gluing-20260930.md)
preserves the state at `28bc4b9`, with relative links relocated. It records
pendant inheritance, the b=1 family and its 58 successful whole layers,
as well as the separately documented eight-vertex enumeration size limit.
Retain all earlier two-clique, terminal-clique, three-chain, complete,
fixed-short, tree, maximum-layer, crossing-slide, packing and attachment
results with their hypotheses. Unrestricted adjacent-swap active membership
remains false; do not reopen that discarded claim.

Primary owns this handoff, the recurrence outline, APPEND-ONLY continuations
of the NN redistribution and DN joint-repair notes, earlier authorized
endpoint/source-addition continuations, handoff archives and existing external
consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and proof-note prefixes at `d7da9ab`.
No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.

The runtime registry, `codex mcp list`, Cargo metadata, Rust library guide
and existing consumer/API code were checked. Lean MCP is rooted at
RealRooted and unused. Maintained Rust is clean at
`24559ad73d209077a58eef08278c425301468cdc`; the final receipt checks it before
and after replay. No worker/account/profile/model assignment changed.
There is no external blocker; the general goal remains unfinished.

The replacement began at account-swap `2511182`. Recent pushed proof
checkpoints are `8149366` (two cliques), `0884521` (minimum-middle DN),
`cf5451e` (pendant/arbitrary-middle DN), followed by metadata `28bc4b9`.
Proof checkpoint `d7da9ab` (last-clique inheritance and the full middle-
position family) is committed and pushed to `origin/main`. Frozen replay,
receipt hashes, preserved prefixes, relocated archive, relative links and
whitespace checks all pass. No verification jobs remain running. The full
general goal remains active and unfinished.

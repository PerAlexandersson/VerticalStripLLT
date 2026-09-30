# VerticalStripLLT handoff

## Current continuation — a uniform three-corner DN recurrence

Primary resumed from clean pushed `0ada933`. The previous and current turns
made verified progress. The full general NN/DN goal remains ACTIVE and
UNFINISHED. Continue the author/Robin diagram method: whole components,
diamonds and justified relabeling. No fundamental basis or substitution
of the separate completed Lean proof.

**New theorem:** the [three-corner DN recurrence](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#a-uniform-three-corner-dn-component-recurrence)
is proved for all maximal-corner sets

    {0a, 1(a+1), ae},       a>=2, e>=a+2.

For its direct DN contact, 0a and ae are strict; the middle corner is
UNMARKED. We prove uniqueness of the connected common-cover component
in every feasible edge layer, then independently reduce every other
source component and subtract from the full DN layer. Every output is
whole and smaller. The same signed recurrence holds for K and E, and
its right-marked version admits arbitrary right attachments.

### The proof

Prepare common-cover states into anchors. Their corner chains are
F={0,a,e}, G={1,a+1}, and singleton vertices. The quotient consists of
K_p and K_q meeting only at F,G, with p=a, q=e-a. Each has one copy of
FG: 1a on the left and (a+1)e on the right. All other classes have one
copy; there are no extra cross edges.

A connected side can be reconfigured at fixed size by complete-cover
paths. On the right use [a,e] with retained ae. On the left, replace 1a
by a(a+1) across 1(a+1) if selected, use the complete graph on [1,a+1]
with retained 1(a+1), then reverse that preparation for the target.
The corner ae may temporarily be redundant, but all three original
corners stay selected. Both endpoints are anchors. Crossing transport
moves 1a to (a+1)e or back, restoring all other edges.

Every selected side is connected or has two components separating F,G.
Both cannot be disconnected if the whole anchor is connected. In a
cyclic layer, at most two shared-edge transfers make BOTH connected:
move a selected nonbridge FG from a connected side if it has a cycle;
if it is a tree, first transfer FG to the other side, which then has
a cycle by the edge count, and transfer back after reconfiguration.

With both sides connected, transfer an edge from a side above its tree
bound to a side below capacity. Put FG on a cycle in the donor and
make it absent in the receiver before sliding. These transfers connect
all feasible allocations, and local complete-cover paths connect all
states within an allocation. The fixed-envelope tree theorem supplies
the remaining tree layer. Preparation (P) extends this to all common-cover
states. Missing corners, weak blocks and alternating corner deletion
reduce every extra component, giving the full recurrence (DG3).

The actual DN target adds 0(a+1) and removes ae, leaving all other natural
edges. It is a pair of cliques meeting at a+1 ONLY when e=a+2. For larger
e, the edges av with a+1<v<e remain; the proof and audits use that full
target. An initial commentary description overstated the split-target
picture and was corrected before checkpointing.

## Verification and receipts

All four final frozen-source replays passed serially at
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-three-corner-recurrences-20260930/`.
All exited zero with empty stderr:

- `--dn-three-corner-paths`: all 36 parameter choices on 5..12 vertices,
  exhaustive cyclic connected anchors through eight, 64 deterministic
  samples per larger graph. 4548 paths / 1291461 globally checked actual
  flips; maximum length 9728. 1886 first preparatory transfers, 140 second
  transfers, 839 allocation transfers. Every endpoint is the prescribed
  canonical anchor for its edge layer. All three corners remain selected.
  No global component search; only the previous fixed K5 base search.
- `--dn-three-corner-layers --right-marked-layers`: all 22 feasible layers
  for all six parameter choices on 5..7 vertices. The middle corner is
  unmarked. 7590 survivor states; 1448 whole targets / 19480 states;
  138 block corrections / 1047 states; 943 missing-corner corrections /
  10337 states; 71 alternating sources / 506 states, yielding 1017 whole
  deletion terms. 1921 positive and 1625 negative terms, 3542 redundancy
  witnesses. Signed marked fibre data, whole outputs and induction order pass.

Two separate exploratory modes use the six three-clique fixtures in
`three_clique_gluing_audit`. Packing and connected two-clique-region moves
alone miss several anchors, including cyclic ones in the nine-vertex
fixture. Adding the already-proved connected-clique-piece moves connects
every layer in those fixtures. These are finite generator graphs, with
each generator justified by an existing path theorem; these modes do not
replay all paths or prove general generation. They are not the proof of
(DG3). The explicit DN path mode above provides its construction.

Only the existing external `dn_joint_span.rs` consumer changed. It reuses
maintained Graph/Poset/HRV APIs and the established actual-flip model.
Python was used only for file bookkeeping and command orchestration.
No new polynomial generator, coloring enumeration, basis calculation,
Lean build or maintained Rust edit ran. Existing enumeration/component
size guards remain. The early Rust type/cast errors were corrected before
the successful runs; they were not mathematical failures.

## Remaining problem

General NN/DN component collection is still unproved outside the established
families and their valid attachments. For example, sources with corners
0a,1c,ae and c>a+1 can have the same DN contact but introduce good cross
edges between left singleton vertices and a+1,...,c-1. The two complete
side graphs used in (DG1) no longer account for every edge. Do not extend
the theorem to that family without handling these cross edges.

The broader three-clique probe suggests that local connected-clique-piece
moves are needed to bring an arbitrary anchor into a state where the two
larger local regions are connected. Their finite generation success is
not a general proof. The two-sided preparation above handles only its
stated quotient geometry. General direct RHS diamond redistribution
remains an alternative to global common-cover uniqueness.

For orientation, the larger-middle geometry already occurs in the old
area-0123343 fixture with corners 03,15,36. It has prior fixed recurrence
checks and counterexamples to stronger completion-class shortcuts; read
[the reduction note](docs/proofs/COMPONENT_RECURRENCE_REDUCTION.md#why-dn-isolation-needs-the-other-reductions)
and [the fixed checks](docs/proofs/COMPONENT_CLOSURE_REPAIR_TESTS.md).
Do not call those already-checked fixed identities newly unsolved. The
missing result is the uniform diagram proof across the larger family.

## Established results to retain

The [previous handoff](docs/archive/component-handoff-before-three-corner-dn-20260930.md)
preserves the full state at `0ada933`, with only relative links relocated.
It includes exact receipts and proofs for:

- Right-marked full-layer recurrences and arbitrary right attachments;
  arbitrary two-end attachments still require both endpoint marks fixed.
- All two-overlapping-clique NN sources, by star normalization, core
  isolation/restoration, and extra-edge rearrangement. This did not by
  itself give a direct DN theorem.
- Terminal-clique and order-dual families, including every ordinary path
  power without divisibility or chain-count restrictions.
- DD/ND inheritance, first-drop induction, fixed-short reductions,
  arbitrary trees, maximum common-cover layers, three-chain families,
  complete diagrams, the stated cubes and earlier fixed examples.
- Preparation (P), arbitrary crossing slides, canonical parallel packing
  and connected pieces inside ANY selected natural cover interval.

Unrestricted adjacent-swap active membership is FALSE already in K5
with strict 04; retain its exact counterexample. A local path establishes
membership, not a state's K/E equality. Canonical anchors cannot replace
whole component sums.

## Ownership and recovery

Primary owns this handoff, the recurrence outline, APPEND-ONLY continuations
of the NN redistribution and DN joint-repair notes, earlier authorized
endpoint/source-addition continuations, handoff archives and existing external
consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and proof-note prefixes at `0ada933`.

No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.
Runtime registry, `codex mcp list`, Cargo metadata, the Rust library guide
and relevant Graph APIs were checked. Lean MCP is rooted at RealRooted
and unused. Maintained Rust was clean at
`24559ad73d209077a58eef08278c425301468cdc` before these new replays; the
receipt records revisions before and after them. No worker/account/profile/
model assignment changed. No external blocker is present.

The replacement originally began at pushed account-swap `2511182`.
Recent pushed proof checkpoints are `4beccde` (right attachments) and
`8149366` (two overlapping cliques), followed by metadata `0ada933`.
All diagnostic jobs are complete. Proof-note prefixes, the relocated
archive, local file links, receipt hashes and `git diff --check` pass
before checkpointing. No process needs monitoring or restarting.
The full general goal is not complete.

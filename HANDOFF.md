# VerticalStripLLT handoff

## Current continuation — terminal-clique NN/DN recurrences

Primary resumed from clean pushed `56a1931`. This turn made verified progress:
a uniform component recurrence for every eligible NN/DN contact when the last
natural clique contains the terminal of every corner chain, and the order-dual
first-clique family. This includes EVERY ordinary path power, for any width
and vertex count. The full general NN/DN goal remains ACTIVE and UNFINISHED.
Continue the author/Robin diagram method; no fundamental basis or substitution
of the separate completed Lean proof.

**New proof:** [terminal-clique recurrence](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-recurrences-when-the-last-clique-contains-every-chain-terminal).
On N vertices the maximal corners are exactly
M={0h_0,1h_1,...,ah_a}, with strictly increasing heads and h_a=N-1.
The d=N-a-1 terminals T={a+1,...,N-1} form the last clique minus its first
vertex. This is equivalent to all terminals lying in that clique.

Every chain pair has one good copy joining its terminal vertices. Hence
its quotient is K_d with positive capacities c_e. The following abstract
occupancy argument is proved for arbitrary capacities, not only equal ones:

1. For connected simple support H and a unit transfer e->f, packing puts
   precisely H-f into the terminal clique, with the receiver absent. A
   direct actual path exists when H-f and (H-e)+f are both connected.
   Use the complete-diagram theorem with its attached corner a(N-1), then
   restore packing. Every original strict edge stays selected.
2. Any transfer preserving global connectedness needs at most one absent
   temporary class g. Failure of the first condition means f is a bridge;
   failure of the second means e is a bridge not reconnected by f, and
   m_e>=2. Choose g across the required bridge cut, or across both cuts
   by joining the outer two of the three pieces after deleting two bridges.
   Then e->g and g->f each satisfy the direct conditions. No capacity is
   exceeded and the temporary class returns to zero.
3. All connected fixed-total occupancy vectors connect. Move a surplus to
   a deficit; if the surplus is a single-copy bridge, choose a deficit
   crossing its cut, which exists because the target support is connected.
   The sum of absolute occupancy differences decreases by two each time.

Thus each feasible source layer has one connected common-cover component.
Every other component independently reduces by an absent corner, weak blocks,
or alternating corner deletion. Full-layer subtraction gives NN target
layers k and k-1, or DN layer k, minus those smaller WHOLE corrections.
Lower/higher layers reduce directly. Correction diagrams need not be in this
family; this is the required induction step, not the full expansion theorem.

Taking h_i=i+d proves every ordinary path-power source, without a divisibility
condition. The order-dual result follows by reversing FLIP PATHS; it does not
assert an order-reversal identity for K/E. The original diagram's own recurrence
is used after transporting the component-uniqueness statement.

**New local lemma:** [connected pieces](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#connected-pieces-inside-a-corner-interval).
For ANY selected natural cover ab, use the weak component B containing a,b
inside [a,b]. Any connected replacement on B of equal size with ab covering
is in the same actual component. Order-compress B and use the complete-graph
proof. Other local components and all exterior edges stay fixed. Directed
cover tests cannot leave the interval or enter another local block. The
retainer may be normal; the entire interval need not be connected.

## Verification and receipt

All five final frozen-source modes exited zero with empty stderr:

- `--terminal-clique-transfers`: all 120 qualifying graphs on 3..8 vertices,
  four larger path powers and one further irregular graph. 2127 occupancy
  paths; 3892 direct transfers and 165 repaired transfers; 4222 local clique
  paths / 313063 actual flips. Maximum path length 6672, up to 52 natural
  edges. Only the previous fixed five-vertex base searches components.
- `--terminal-clique-layers`: 19 whole NN/DN source layers, 52776 survivor
  states; 1193 whole target components / 88880 states; 216 block corrections /
  3364 states; 587 missing-corner corrections / 30251 states; 276 alternating
  source corrections / 2489 states, yielding 4888 whole deletion terms.
  Totals: 3499 positive and 3385 negative terms, 32247 redundancy witnesses.
  Both block flip directions and every smaller-diagram condition pass.
- `--complete-swap-audit`: checks all middle states through six vertices and
  prints an exact five-vertex counterexample to unrestricted active membership.
- `--local-clique-anchor-generators`: nine fixtures, with every chosen local
  path replayed globally. Packing plus all selected-cover clique moves connects
  each connected occupancy layer in the eight non-articulation fixtures. This
  is finite evidence, not a new general generation theorem.
- Same generator mode with `--maximal-cliques-only`: misses one tree anchor in
  area 0123434 (104+1 instead of 105). Normal retained covers recover it. The
  two-K4 articulation control retains its known two middle-layer components.

Receipt, frozen sources, commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/terminal-clique-recurrences-20260930/`.
Only the existing external `dn_joint_span.rs` consumer changed. Graph and Poset
APIs and the actual-flip model are reused. No Lean build, worker, maintained
Rust edit, coloring or basis calculation ran. The 21-edge full-enumeration and
20000-state component guards remain. Larger graphs use explicit paths only.

For the DN fixture with heads [3,4,5,7], 14 is UNMARKED: the contact (0,3,4,7)
introduces strict 04, which would contain it. The final audit uses eligible
strict edges 03,25,37 and includes the missing-14 source sector. The earlier
trial marking all four corners was invalid and was corrected, not accepted.

## What remains open

General NN/DN collection remains unproved outside the terminal-clique and
order-dual conditions and the previously established families. In general
there need not be one natural clique containing a good copy of every chain
pair. A promising next problem is to coordinate the local connected-piece
moves across overlapping cliques, together with unrestricted packing. This
requires a proof of generation, not extrapolation from the nine fixtures.
Direct RHS repairs and justified relabelings remain permitted alternatives.

Do NOT use an unrestricted adjacent-swap membership assertion, even at a
leftmost NN contact. The exact [counterexample](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#why-the-adjacent-swap-still-needs-a-repair)
has strict 04 and A={02,03,04,12,14,23,24}. Six written flips make 04 cover,
but swapping 0,1 sends A to a closed nine-state component where 04 is always
redundant. The complete-diagram recurrence already handles it by independent
inactive-corner reduction. The failed shortcut is not an unresolved recurrence.

The local lemma is a component-membership assertion, NOT equality of a state's
K/E value before and after a flip. Likewise canonical anchors cannot replace
whole component sums. Endpoint extensions still require the actual recurrence
and all its relabelings to preserve the attachment endpoint.

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

Primary owns this handoff, the recurrence outline, APPEND-ONLY continuations
of the NN redistribution and DN joint-repair notes, earlier authorized
endpoint/source-addition continuations, handoff archives and existing external
diagnostic consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and both proof-note prefixes at `56a1931`.

No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.
Runtime registry, `codex mcp list`, current Cargo metadata and relevant
Graph/Poset/actual-flip APIs have been checked. The Rust guide was already
read in this continuation chain. Lean MCP is rooted at RealRooted and unused.
Maintained Rust remains clean at `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
No worker/account/profile/model assignment changed.

The replacement originally began at pushed account-swap `2511182`. The full
handoff at `56a1931` is preserved in the
[pre-terminal-clique archive](docs/archive/component-handoff-before-terminal-clique-20260930.md),
with only relative Markdown links relocated. It retains the complete-diagram
proof checkpoint `4ca99c3`, receipts and earlier recovery links.
All diagnostic jobs are complete; no process needs monitoring or restarting.

Both proof-note prefixes, the exact relocated archive, 155 local file links,
final frozen-source replays and receipt hashes pass before checkpointing.

Proof checkpoint `c2fc099` is pushed to `origin/main`; `git diff --check`
also passes. All five diagnostic jobs are complete. The full general NN/DN
goal remains active, with no external blocker or running process.

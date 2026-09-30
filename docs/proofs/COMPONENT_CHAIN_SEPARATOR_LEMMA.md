# Deleting a corner chain

We give a shorter proof of the separator assertion used in the ordinary
component argument. Let G be a connected ordinary natural graph on
0,...,n-1, where n≥3, and suppose that G has no articulation. Let M be a
family of maximal natural corners containing all strict edges. Write r(v)
for the terminal vertex of the M-chain containing v. As before, A* consists
of M and the natural edges uv with r(u)<r(v).

**Lemma.** Deleting any one M-chain from A* leaves a nonempty connected
graph. If there are at least three M-chains, every edge of A* outside M
can be deleted without disconnecting A*.

**Proof.** We first show that every edge of length one or two is natural.
A natural path from i to i+1 has an edge crossing the cut between them.
Closure under subintervals gives the edge i(i+1). For i and i+2, choose
a path avoiding i+1. Some edge of that path joins a vertex at most i to
a vertex at least i+2, so i(i+2) is natural as well.

No retained corner can join consecutive vertices i,i+1. If i>0, the
natural edge (i-1)(i+1) properly contains it. If i=0, the natural edge
02 properly contains it. Furthermore, two consecutive vertices of the
same M-chain would give a natural edge inside that chain, hence a retained
corner. Thus no M-chain contains consecutive vertices.

Fix a chain B. In the increasing list of vertices outside B, consecutive
entries differ by at most two. They are therefore joined by natural edges.
At least one vertex survives, since 0 and 1 belong to different chains.
This proves connectivity in the natural graph after deleting B.

We replace these natural edges by paths in A*. A natural edge uv is already
in A* unless r(v)<r(u). In the latter case, let uh be the next retained
corner from u. We have u<v<h, and the natural edge vh satisfies
r(v)<r(h)=r(u). Replace uv by the undirected path u,h,v. Its new vertex h
belongs to the same chain as u. Hence a natural path outside B becomes
a path in A* outside B.

Now let d=uv be an edge of A* outside M. Its endpoints belong to different
chains, say B and C. Choose w in a third chain. There is a path from u to w
outside C and a path from w to v outside B. Neither path uses d. Their
concatenation connects the endpoints of d after its deletion, so replacing
each occurrence of d in a path proves that A* minus d is connected.

**Corollary.** Under the same assumptions and with at least three chains,
let d belong to A* outside M. For every n-1≤k<|A*|, there is a connected
anchor with k edges that omits d. All edges of M are retained and cover.

We apply forest extension in A* minus d, retaining the forest M. This
produces the required selected edge set, and every subset of A* containing
M is an actual simultaneous-cover anchor.

## Formalization record

Related Lean: all files below are in
`../../VerticalStripLLT/Components/DiagramProof/`.

- `NaturalSeparators.lean`: `naturalEdgeRelation_short_of_connected_of_delete`
  proves the short-edge consequence. The converse is recorded by
  `naturalEdgeRelation_connected_of_short` and
  `naturalEdgeRelation_delete_of_short`.
- `IntervalDeletion.lean`: `eqvGen_of_short_edges_of_no_consecutive_omissions`
  gives the path after deleting a set without consecutive vertices.
- `ChainSeparators.lean`: `terminal_ne_of_consecutive` and
  `goodEdge_weakReach_avoiding_terminal` specialize to corner chains.
- `QuotientSeparators.lean`: `chainQuotient_induce_connected_avoiding_terminal`
  states the corresponding quotient-vertex deletion result, including
  nonemptiness.
- `RemovableGoodEdges.lean`: `goodEdgeGraph_delete_connected_of_no_articulation`
  gives the actual good-edge deletion statement.
- `exists_connected_anchor_card_avoiding_of_no_articulation` gives the
  corollary as an actual orientation with exact cardinality and edge absence.

These results concern graph paths and existence of anchors. The component
inheritance and terminal-clique transfer proofs still require formalization.

# Unicyclic components after articulation decomposition

2026-09-28. We investigate the remaining NN isolation question by a
stronger structural statement: in a saturated ordinary natural graph
without an articulation vertex, is there at most one surviving connected
unicyclic component? Here surviving means that some state has an acyclic
mixed graph, with strict edges reversed. The statement remains unproved.
The lemmas and local paths below are proved and independently audited;
the finite search is evidence only. The full component recurrence remains open.

The distinction between natural blocks is necessary. Two complete graphs
on four vertices joined at one vertex have distinct surviving unicyclic
components, according to which block contains the cycle. See
[the exact articulation example](COMPONENT_ACTIVE_CORNERS.md). We cannot
replace blockwise edge counts by the total selected-edge count.

## Contracting the strict chains creates no new articulation

Let G be a connected ordinary interval-closed graph on 0,...,n−1, n≥3,
and let S be its maximal intervals. Suppose G has no articulation vertex.
The edges of S form disjoint increasing chains, including isolated vertices.

**Lemma.** Contract each strict chain and delete the contracted strict
edges. The resulting multigraph is connected, has no loops, and remains
connected after deleting any one vertex. If it has only two vertices,
at least two parallel edges join them.

First, G has no articulation vertex exactly when every distance-two edge
(i,i+2) is natural. If that edge is missing, interval closure excludes
every edge crossing the intermediate vertex i+1, making it an articulation.
Conversely, after deleting one vertex, consecutive surviving labels differ
by at most two and are therefore joined by natural edges.

It follows that every strict corner has length at least two. No strict
chain C contains consecutive labels. After deleting all vertices of C,
consecutive remaining labels still differ by at most two. Thus G−C is
connected. Contracting its remaining strict chains proves the assertion
about deleting a vertex of the quotient. We count a singleton as connected.

A normal edge cannot join vertices of one strict chain: the chain segment
between them would contain a strict edge inside that normal interval,
contradicting maximality. Hence the quotient has no loops. If its two
vertices had only one edge between them, G would be a tree on at least
three vertices, contradicting the absence of an articulation. This proves
the lemma. We avoid calling a two-vertex underlying simple graph biconnected.

The lemma rules out an additional cycle-location obstruction coming from
an articulation created by contraction. It does not identify actual flips
with arbitrary edge exchanges in the quotient.

## Why contracting the smallest cycle vertex can stop early

Take area (0,1,2,3,3), with strict corners 03,14, and select

    A={02,03,12,14,34}.

Every selected edge covers, and the mixed graph is acyclic. The unique
undirected cycle is 0–2–1–4–3–0. The actual flip 02→23, retaining 03,
contracts its smallest vertex out of the cycle. Its result is

    {03,12,14,23,34}.

The remaining four-cycle has strict edge 14 redundant through 12,23,34.
We cannot contract its smallest vertex by retaining 14. Thus redundancy
may appear before a triangle is reached, even inside a surviving component.

Nor can we insist on reaching a triangle with normal long edge. In the
square of a four-vertex path, with strict corners 02,13, the three normal
pairs {01,12}, {01,23}, {12,23} form one surviving unicyclic component.
Every normal edge is adjacent and always covers. The middle state has a
four-cycle; the other two have a redundant strict edge.

## Restoring the smaller envelope after making the first vertex a leaf

By [corner leaf normalization](COMPONENT_TREE_CONNECTIVITY.md), a surviving
unicyclic component has a state in which vertex 0 is a leaf attached to
the right endpoint r of its strict corner 0r. Indeed, the
[unicyclic classification](COMPONENT_UNICYCLIC_REDUNDANCY.md) implies that
0r covers somewhere in the component. Deleting the leaf leaves a unicycle.
Its selected envelope need not be the whole induced natural graph on
1,...,n−1; restoring that envelope would be a useful next step.

Even with the full envelope, the smaller component need not survive.
In the four-vertex example above, the only leaf-at-0 state is
{02,13,12,23}. Deleting 0 leaves the full triangle {12,13,23}, whose
strict corner 13 is redundant throughout its singleton component.
Thus an induction must retain these smaller inactive components too.

There is also a cover obstruction to copying the tree-normalization
path verbatim. In the complete graph on five vertices, with 04 strict,
start at the leaf state

    A={04,12,13,24,34}.

The smaller envelope has maximal intervals 13,24 and omits 14. The
two tree-sweep moves 24→02, retaining 04, and 12→01, retaining 02,
are actual. They produce {04,02,01,13,34}. But 04 is now redundant
through 01,13,34, so we cannot make the next move 01→14 retaining 04.
The other path through the cycle fails in the same way.

One preliminary flip repairs this example. The following complete path
restores the smaller envelope while returning 0 to a leaf.

| Retained edge | Exchanged edges | Resulting selected set |
| --- | --- | --- |
| 13 | 12 → 23 | {04,13,23,24,34} |
| 04 | 34 → 03 | {04,03,13,23,24} |
| 03 | 13 → 01 | {04,03,01,23,24} |
| 04 | 01 → 14 | {04,03,14,23,24} |
| 04 | 03 → 34 | {04,14,23,24,34} |

Only 24 is redundant after the first move. All edges cover after the
second move, and the next two moves transfer a pendant branch. In the
last state 24 is redundant again. It is never a required cover in the
table. Thus every row is an actual flip and retains 04. This repairs
one configuration; a uniform envelope-restoration argument is still needed.

## Exact search and scope

The existing actual-flip enumerator checks every saturated ordinary
natural graph without an articulation on seven and eight vertices.
Such area sequences start with 0,1 and have every later entry at least
two. The ordinary area condition enumerates exactly these graphs.

| Vertices | Natural graphs | Connected unicyclic states | Surviving components |
| --- | ---: | ---: | ---: |
| 7 | 42 | 59,881 | 42 |
| 8 | 132 | 1,280,832 | 132 |

Each graph has exactly one surviving component in this range. Each such
component also contains a leaf-at-0 state whose remaining envelope is the
full induced natural graph. These are exhaustive finite assertions about
actual components. Neither property is inferred for larger graphs, and
we have not proved that the first property follows from the second.

The five-flip repair also passes exact cover checks. Primary and Astra
independently checked the structural lemma, the examples and the path.
No component polynomial equality is inferred from a partial state sum.

Related Rust: the external consumer `unicyclic_blocks.rs` reuses
`component_source_probe.rs::{make_model,component,flip,projected_acyclic}`
and `combinatoric_core::graph::Graph::is_connected`. Frozen sources, Cargo
files, commands and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-blocks/`.
No maintained Rust, Lean or manuscript sources were changed.

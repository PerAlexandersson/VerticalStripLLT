# Redundant edges in unicyclic components

2026-09-28. We prove that a connected ordinary component whose selected
graphs have one undirected cycle contains a state in which every normal
edge is a cover, provided all natural corners are strict. This gives a
structural reason that unicyclic components admit minimal representatives.
It does not supply the general component reconstruction after NN.

We use the ordinary actual flips and the
[tree-connectivity theorem](COMPONENT_TREE_CONNECTIVITY.md). Every edge
points forward in the vertex order. A selected edge is redundant if its
endpoints are joined by another directed path. A connected unicyclic
state has n selected edges on n vertices. Flips preserve connectedness
and edge count, so the condition holds throughout a component.

## Redundancy cannot move directly to another edge

**Lemma.** A unicyclic state has at most one redundant edge. If two
unicyclic states are joined by an actual flip and both have a redundant
edge, that edge is the same in both states.

An edge together with its directed bypass gives an undirected cycle.
There is only one such cycle. Traversing it along the bypass, all edges
except the redundant edge point forward, and that edge points backward.
This also proves uniqueness of the redundant edge.

Let e be redundant before a flip. It can be neither the retained long
nor the exchanged short, since those edges must be covers. If the flip
does not delete a bypass edge, e remains redundant and uniqueness proves
the claim.

Suppose instead that the deleted short lies on the bypass. The retained
long is not another cycle edge: consecutive bypass edges meet head to
tail, whereas a long edge and one of its shorts share a tail or a head.
The only other cycle edge is e, which is not a cover. Thus the retained
long is a bridge, and its other endpoint lies outside the cycle.

The flip replaces one forward cycle edge by a two-edge detour, one edge
forward and one backward. The new cycle therefore has at least two edges
in each direction. No edge has a directed bypass around this cycle, and
bridges cannot be redundant. The new state has no redundant edge, proving
the lemma.

## Deletion gives a whole tree component

**Corollary.** Let C be a connected ordinary unicyclic component. Either
C contains a state in which every normal edge is a cover, or one normal
edge e is selected and redundant throughout C. In the latter case,
deleting e maps C bijectively onto a whole tree component with the same
K and E sums.

If the first alternative fails, every state has a redundant normal edge.
The lemma says this edge cannot change across an actual flip. Connectedness
of C makes it common to all states. The
[whole-component deletion lemma](COMPONENT_CLOSURE_REPAIR_TESTS.md)
then applies. Deleting a redundant edge preserves connectedness and
reduces the selected count from n to n−1, so the image is a tree
component. Both valuations are preserved state by state. In particular,
the existing forest-component theorem proves K(C)=E(C) in this case.

The unique cycle in this second alternative is entirely normal: every
bypass edge lies properly inside the interval e, so cannot be a strict
corner. All strict edges are bridges. Reversing them leaves an acyclic
mixed graph. Thus this reduction need not initially be detected by a
mixed-cycle test. Saturating the selected envelope may change that test.

## Saturation excludes the second alternative

**Theorem.** Suppose every maximal interval of the ordinary natural graph
H is strict. Every connected unicyclic complete component has a state
in which all normal selected edges are covers.

Let S be the strict corner set. Its edges form disjoint increasing chains:
maximal intervals have at most one edge starting or ending at each vertex.
If e is a normal natural edge, its endpoints cannot belong to one chain
of S. Otherwise the chain segment between them contains a strict edge
properly inside e, contradicting maximality of that strict edge.
Consequently S together with e is a forest.

Suppose the second alternative of the corollary holds. Delete the common
redundant normal edge e to obtain a whole tree component C′. Every tree
in C′ contains S, so its interval envelope is exactly H.

The graph H is connected, since it contains a connected source state.
Extend the forest S together with e to a spanning tree T in H. This tree
also has envelope H, since it contains every maximal interval. The
tree-connectivity theorem places T in C′. But every tree in C′ omits e,
whereas T selects e. This contradiction proves the theorem.

For a nonsaturated component, we may first pass to its selected interval
envelope and mark all maximal intervals strict. Flips preserve this
envelope, and every maximal interval is necessarily selected. These
intervals cannot be exchanged shorts, so marking them strict does not
change the component. The theorem then says that C contains a state
whose only possible redundant edge is maximal in that selected envelope.

## Relation to reconstruction and checks

For a state with reachability P, being minimal among states with the same
reachability and strict set S means exactly that its selected set is
Hasse(P)∪S. Equivalently, every normal selected edge is a cover. Thus the
theorem proves the minimal-representative property for saturated
unicyclic components. Even without saturation, the corollary proves a
useful column statement: a connected unicyclic component either contains
a minimal representative, or has exactly the same closure/swap column
as a whole tree component. Tree states are minimal representatives.
Thus every such column is supplied by the minimal-representative columns.

These conclusions do not extend to arbitrary components with several
cycles; the failed minimal-column restriction in the
[closure repair tests](COMPONENT_CLOSURE_REPAIR_TESTS.md) remains a
counterexample to that proposed general reconstruction.

Astra supplied the cycle argument and its saturation proof; primary
checked the cover tests, whole-component deletion and tree extension.
The Rust check enumerates every saturated ordinary diagram on three
through six vertices. It checks the no-change lemma across all 12,794
directed flips in 156 connected unicyclic components, and verifies that
each component has a state with all normal edges covering. These finite
checks support the proofs above and are not their justification.

Related Rust: `audit_unicyclic` in the frozen external
`nn_capacity_repair.rs` consumer. Receipt `unicyclic.jsonl` is under
`/lake-cache/ai-projects/requests/VerticalStripLLT/deficit-repair/`.
No Lean or manuscript source is changed.

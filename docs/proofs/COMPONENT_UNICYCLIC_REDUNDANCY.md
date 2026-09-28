# Redundant edges in unicyclic components

2026-09-28. We prove that a connected ordinary component whose selected
graphs have one undirected cycle contains a state in which every normal
edge is a cover, provided all natural corners are strict. This gives a
structural reason that unicyclic components admit minimal representatives.
We also classify the wholly mixed-cyclic components and control two
families of NN corrections. The general component reconstruction remains open.

We use the ordinary actual flips and the
[tree-connectivity theorem](COMPONENT_TREE_CONNECTIVITY.md). Every edge
points forward in the vertex order. A selected edge is redundant if its
endpoints are joined by another directed path. A connected unicyclic
state has n selected edges on n vertices. Flips preserve connectedness
and edge count, so the condition holds throughout a component.

The subsequent [leftmost NN theorem](COMPONENT_LEFTMOST_NN_UNICYCLIC.md)
closes all these joins for a=0 in cycle rank one. Statements below
about remaining middle/first joins concern general a unless specified.

## Redundancy cannot move directly to another edge

**Lemma.** A unicyclic state has at most one redundant edge. If two
unicyclic states are joined by an actual flip and both have a redundant
edge, that edge is the same in both states.

An edge together with its directed bypass gives an undirected cycle.
There is only one such cycle. Traversing it along the bypass, all edges
except the redundant edge point forward, and that edge points backward.
This also proves uniqueness of the redundant edge.

For an actual flip, write its endpoints as Z+ac+ab and Z+ac+bc.
The graph T=Z+ab+bc is connected and unicyclic too. Every edge redundant
at either endpoint remains redundant in T, since ab,bc simulate ac.
Two different redundant edges at the endpoints would therefore give
two redundant edges in T, contradicting uniqueness. This proves the
lemma. The [redundancy diamond](COMPONENT_REDUNDANCY_DIAMOND.md)
proves the stronger equality of redundant-edge sets and its general
cycle-rank bound.

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

## Exactly which unicyclic components are wholly mixed-cyclic

Reverse every strict edge, retaining the forward orientation of normal
edges. We call this the mixed graph of the state.

**Theorem.** A connected ordinary unicyclic component has a directed
cycle in every mixed graph if and only if one strict corner is redundant
throughout the component. This corner is unique.

For the nontrivial implication, consider a mixed-cyclic state A. Its
directed cycle is the unique undirected cycle. Suppose this cycle contains
at least two strict edges. Every selected edge is then a cover in the
forward graph. Indeed, a redundant edge and its bypass would form the
unique cycle; every other edge of that cycle would lie properly inside
the redundant edge's interval, so none could be a strict corner.

The mixed directed cycle contains both strict and normal edges: the
former point backward and the latter forward. Choose a transition
c→a→b where ac is strict and ab normal. Maximality of ac gives a<b<c.
The actual flip retaining ac and replacing ab by bc is therefore valid.
In the new unique cycle, bc and the former remaining path from b to c
both point from b toward c in the mixed orientation. The cycle is no
longer directed. Thus a wholly mixed-cyclic component cannot contain
the state under consideration.

Every state of such a component consequently has exactly one strict
edge on its cycle. All remaining cycle edges form its forward bypass,
so that strict edge is redundant. The no-change lemma above makes it
the same edge throughout the component. Conversely, a redundant strict
corner together with its bypass becomes a directed mixed cycle: all
bypass edges lie properly inside the corner and are normal. Uniqueness
follows from the unique undirected cycle.

Deleting the common corner g gives a whole tree component. By
[forced tree reachability](COMPONENT_TREE_CONNECTIVITY.md), its maximal
intervals M contain an increasing chain between the endpoints of g.
Conversely, inserting g into such a tree component gives precisely an
inactive unicyclic component. We have therefore described all the
unicyclic components discarded by the mixed-cycle reduction.

## Inactive corners other than the NN corner stay separate

Use the NN setting of
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md): f=ac is strict,
b=a+1, q=ab, r=bc, and σ exchanges a,b. The NN hypotheses imply that
every natural edge leaving a or b ends at or before c, and no strict
edge ends at a or b. We use complete connected unicyclic source components.

**Lemma.** If one endpoint of a packet join is a component inactive at
a strict corner g≠f, the other endpoint is also inactive at g.

Delete g from a state at the first endpoint. This gives a tree with
envelope H. Its maximal intervals M contain the forced bypass of g.
They also contain f. This bypass avoids a,b: at a the only possible
maximal outgoing interval is f, and at b there is no maximal outgoing
interval, since all its outgoing intervals lie properly inside f.
The bypass lies inside g and therefore cannot use f. Neither a nor b
can be its terminal vertex, by the strict-head hypothesis.

For a middle join or a right mixed join, the selected edges change only
by σ on the exterior and by changes inside f; f remains selected. Every
edge of the bypass has both endpoints outside {a,b}, so σ fixes it.
Since a,b are adjacent, swapping an interval's endpoints by σ does not
change whether it contains one of these fixed bypass intervals. Added
edges inside f cannot contain a bypass interval either, since that
interval was maximal alongside f. Thus the bypass edges remain selected
and maximal after deleting g at the other endpoint.

A left mixed join has t<a<b<c and retains tb. It can also change ta,
which lies outside f. This cannot remove a bypass edge, since the bypass
avoids a. Inserting ta cannot contain a maximal bypass interval either:
the common selected tb already contains ta. Thus the same conclusion
holds for the left mixed joins.

The packet invariant preserves connectedness and the unicyclic edge
count. The retained bypass makes deletion of g a tree again. Its
maximal intervals still force the bypass, so the whole component at
the other endpoint is inactive at g, by the tree theorem. This proves
the lemma for all three kinds of NN join.

Consequently, a packet containing a surviving unicyclic component
contains no component inactive at any corner other than f. This is a
statement about arbitrary paths of joins, not just one chosen state.

The lemma does not say that these inactive components are identical.
For example, take area (0,1,2,3,4,5,6,4,5), strict corners g=06 and
f=38, and the NN step at 3<4<8. Put

    A = {06,02,26,13,38,35,45,68,78},
    B = {06,02,26,14,48,35,38,68,78}.

After deleting g, these are trees with maximal intervals respectively
{02,13,26,38} and {02,14,26,38}. Both contain the forced chain 0→2→6,
so they belong to inactive-g components. Those components are distinct:
their deletion-tree envelopes differ. Yet R₀=σA admits the target flip
45→34 retaining 35, and its result R₁ satisfies B=R₁−34+38. This is
exactly a first mixed packet join. The conclusion needed above is
preservation of the inactive corner, not equality of these components.

## Two inactive-f families have controlled neighbors

Let I be inactive at f, and let its deletion-tree envelope have the
forced maximal chain

    a=x₀ < x₁ < ⋯ < x_k=c.

Suppose this chain contains b. Since b=a+1, we have x₁=b.

If k=2, both q and r are maximal intervals of the deletion envelope,
so both are selected throughout I. There is no middle join or first
mixed join incident to I, by their q,r strata. A second mixed join
would require a target flip exchanging q, with a selected retained
long interval properly containing q. That interval is also selected
in the source after deleting f, contradicting maximality of q.
Thus I is an isolated vertex of the packet graph.

If k>2, q is selected and r absent throughout I: selecting r would
contradict maximality of the proper intervals on the suffix of the
chain. Only middle joins can occur. Their other endpoints are the
states

    A − q + r,       A ∈ I.

This entire family is connected by actual source flips. Every flip in
I avoids q: no selected long interval other than f contains q, and
the redundant f cannot support a flip. Deleting q preserves all the
required cover tests. The remaining fixed chain b→⋯→c makes r
redundant, so inserting r changes no reachability or cover test for
the retained edges. Every original flip therefore lifts to its displayed
image.

Hence all middle joins from I reach the same complete source component.
This component survives the mixed-cycle reduction. The unique cycle
in each displayed image consists of r and the normal suffix b→⋯→c;
all strict edges are bridges. Its mixed graph is acyclic. We have proved
that I has exactly one neighboring component in the packet graph.

What remains in the inactive-f analysis is the forced chain that skips b.
Here r is absent throughout, but q can vary. Middle joins and first
mixed joins must be shown to reach the same surviving component. In
addition, joins whose two endpoints already survive need an actual
source-connectivity proof. None of the lemmas above proves that step.

There is a reduction for this skipped-b case. On each connected piece
of the q=1 subgraph of I, the map A↦A−q+r lifts every flip. The fixed
f-bypass omits b and survives the replacement. Each image is connected
and unicyclic, with f its sole redundant edge, so the other edges
required by a transported flip cover.

Every first mixed join incident to a q=0 state also corresponds to
an actual q-changing flip inside I. In the right case, its source
contains {f,ad,bd} and we exchange bd with q, retaining ad. In the
left case it contains {f,ta,tb} and we exchange ta with q, retaining
tb. These are covers because only f is redundant. The first-mixed
neighbor and the middle neighbor of the resulting q=1 state differ
by an exterior swap:

    S₀∪T∪{f,ℓ,r},       S₀∪σT∪{f,ℓ,r},

where ℓ=ad or tb. This identifies the comparison at each entrance
or exit of a q=0 piece. A path through I may have several consecutive
q=0 states; propagation across that entire piece remains unproved.

One right second mixed join reduces, by an actual flip, to comparing

    S₀ ∪ T ∪ {ac,ad,bd,bc},
    S₀ ∪ σT ∪ {ac,ad,bd,bc},       a<b<d<c,

where S₀ consists of the other strict edges. This comparison is now
proved in [the four-cycle swap theorem](COMPONENT_FOUR_CYCLE_SWAP.md),
including incoming branches whose containing strict corner lies in a
different attached tree. We first normalize that tree, move the cycle
to meet the corner, transfer the incoming branch by six flips, and
undo the temporary moves. The same note now proves the left four-cycle
swap by converting to a right core. Thus both second mixed joins stay
within one connected unicyclic component. The surviving-to-surviving
middle and first mixed joins remain open. The same note now proves
full σ-invariance of a q-free state selecting f,r whenever its unique
cycle contains either edge. In particular the 01 endpoint of every
nonactual middle join is σ-invariant within its component. This does
not identify it with the 10 endpoint. The right held-edge replacement
is now proved separately in
[the outgoing-edge transfer](COMPONENT_RIGHT_ARM_TRANSFER.md), including
on-cycle cases; it does not settle the preceding middle join. The same
note gives distinct inactive components showing that a general incoming
replacement is false.

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

The later mixed-cycle classification and NN packet lemmas were derived
by primary and the independent Astra reviewer, who audited the complete
arguments. A finite check of all 76 eligible NN instances through n=6
counts 99 connected unicyclic component occurrences: 22 surviving and
77 wholly mixed-cyclic. The latter are exactly those with a common
redundant strict corner. All 46 distinct intercomponent joins have an
inactive-f endpoint and a surviving endpoint in this range. The two
seven-vertex fixtures area0123434 and area0123343 satisfy the same
proved predicates. The checks also verify the two neighbor conclusions
when the forced bypass contains b; the skipped-b case remains a
conjectural connectivity statement despite these finite successes.

Related Rust: `nn_component_transport.rs`, modes
`--scan-unicyclic-packets --audit-unicyclic-packet-edges` and the two
seven-vertex fixture flags. Frozen sources, manifest, lock, commands,
receipts and hashes are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-packet/`.

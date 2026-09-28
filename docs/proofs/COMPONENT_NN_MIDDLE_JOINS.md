# Middle joins for general unicyclic NN steps

2026-09-28. We prove that every f-active middle join is internal to
an actual component, at every eligible saturated ordinary NN position.
The proof constructs a tree with an exposing flip, rather than requiring
a prescribed edge to remain selected along a tree-normalizing path.
First mixed joins and the other recurrence steps remain separate.

## The maximal-edge forest

We retain the saturated ordinary NN hypotheses from
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md). Write
f=ac, q=ab and r=bc, with b=a+1. The corner f is strict; the other
strict corners avoid a,b. All selected edges point forward.

Let A=T+f be a connected unicyclic selected state in which f is
redundant, q is selected and r is absent. Then T is a tree. Write
H=Env(T), let M be its maximal intervals, and put F=M∪{q}.
The envelope H omits f,r and contains every other original strict
corner. Its maximal intervals form disjoint increasing chains.

No edge of M ends at a. Indeed, any maximal natural interval of
the original diagram containing such an edge is different from f.
It is strict by saturation and belongs to T, so maximality in H
would make it the same edge. This contradicts the NN prohibition
on strict heads at a. The same argument excludes edges of M ending
at b with tail less than a; the only possible remaining edge is q.

Consequently F is a forest. Its component containing a is directed
away from a: it is either one increasing chain, or the two increasing
chains starting at a and b, joined by q. Every other component is
an increasing M-chain.

## Constructing a q-preserving exposing flip

**Lemma.** Suppose F has no directed a-to-c path. Then there is a
spanning tree T* with envelope H containing F such that a reaches c
in T*, and an actual flip of T*+f preserves F and makes f a cover.

We start with the increasing a-to-c path P in T. Since F has no
such path, we can choose an edge e=xy of P outside F. Choose a
maximal interval g=uv in M containing e. This containment is proper,
since e∉M.

The graph Z=F∪P is a forest, being a subgraph of T. Removing e
separates its path-containing tree into a part L containing a,x
and a part R containing y,c. The edge g belongs to F, so its
endpoints remain in the same component of Z−e.

**Case 1: g belongs to neither L nor R.** Its F-component is
disjoint from P. Thus u<x<y<v. Adjoin xv to Z; this connects two
different components and remains a forest. Extend it to a spanning
tree T* of H. The path P remains the unique a–c path. The flip

    xy → yv, retaining xv,

replaces part of that path by x→v←y. Hence f covers after the flip.

**Case 2: g belongs to L.** We claim that u is reachable from a
in Z−e. If g lies in the F-component containing a, this follows
from its outward orientation established above.

Otherwise g lies in an increasing M-chain which meets P. The
intersection of two subtrees of a forest is connected. This chain
therefore meets P in a single subpath. Since g skips the open
interval (u,v), and P uses the properly contained edge xy, that
intersection lies entirely before u or entirely after v: meeting
both sides would force P to use g. Membership in L excludes the
latter possibility. We can thus follow P to an intersection vertex
k≤u, and then follow the M-chain from k to u.

Adjoin uy to Z−e. It reconnects L to R and gives a forest with
an increasing a-to-c path through uy. We have y<v, since otherwise
y=v would already belong to L. Extend this forest to a spanning
tree T* of H and use

    uy → yv, retaining uv.

The unique a–c path now traverses u→v←y, so f becomes a cover.

**Case 3: g belongs to R.** Its F-component is an increasing
M-chain, since the exceptional component contains a and lies in L.
The same intersection argument shows that this chain meets P after
v. Thus c is reachable from v in Z−e. Adjoin xv to Z−e and extend
to a spanning tree T* of H. The unique a–c path is increasing,
and u<x because u=x would put g in L. The flip

    xv → ux, retaining uv,

changes that path to include x←u→v, making f a cover.

In each case the prescribed forest contains M, so its tree extension
has envelope H. The exchanged short is outside F: in Cases 2 and 3
it connects two components of Z−e, which already contains F, and
in Case 1 it is e. Thus q and every original strict corner other
than f remain selected. The retained long and exchanged short are
covers in the tree. Inserting the maximal f does not affect their
cover tests, so every displayed flip is actual in the original
diagram. This proves the lemma.

## All active middle joins are internal

**Theorem.** Let C be a connected unicyclic component in an eligible
saturated ordinary NN diagram. Suppose f covers in some state of C.
For every A∈C selecting q and omitting r, the middle image A−q+r
also belongs to C.

If f covers in A, the flip q→r retaining f proves the claim.
Otherwise put T=A−f and use H,M,F as above. The maximal forest M
cannot force a→c: by the
[forced-tree-path theorem](COMPONENT_TREE_CONNECTIVITY.md), inserting
f into that entire tree component would otherwise give an inactive-f
component, contradicting the hypothesis on C.

If F forces a→c, the proposition in
[the leftward-transition note](COMPONENT_LEFT_EXIT.md) already proves
the claim. Suppose F does not force this path. The new lemma supplies
T* with q selected, f redundant in A*=T*+f, and a q-preserving flip
from A* which makes f cover.

Tree connectivity in H lifts after inserting maximal f, so A*∈C.
The exposing flip also lifts after q is replaced by r, by the
[q-preserving lifting lemma](COMPONENT_NN_INACTIVE_CORRECTIONS.md).
At the exposed state the middle flip q→r retaining f is actual.
These three connections give A*∼A*−q+r.

Finally, the redundant middle-image lemma in that same note connects
A*−q+r to A−q+r: the deleted-f trees have the same envelope H,
both select q, and both have a directed a-to-c path. Thus A−q+r∈C,
as required.

## Remaining ordinary recurrence work

This theorem settles all middle joins for connected unicyclic NN
components. The earlier inactive-correction theorem controls middle
joins from inactive-f components, and components inactive at another
corner satisfy the separate corner-label invariant.

First mixed joins still require attention when the unique selected
cycle avoids both f and r. The existing swap and incoming-bridge
theorems require the cycle to use at least one of these edges.
The reductions below narrow this issue further. The subsequent
[first-join tree comparisons](COMPONENT_NN_FIRST_JOINS.md) also handle
a least incoming tail and incoming bridges with a strict covering
container anywhere in the graph. They now settle both first joins for
mixed-acyclic representatives whose cycle avoids a,b. This does not supply
those hypotheses at every representative or settle all first joins.
The DN/DD steps, recurrence coverage and higher cycle ranks also
remain. The user has made the circular extension optional; the
current proof target is the ordinary component formula.

### Cycles in another natural block

Suppose the unique selected cycle lies in a different biconnected
block of the natural graph from f. Every natural edge incident to
a or b belongs to the block containing f. Outgoing edges at these
vertices lie inside f. An incoming edge ta with t<a has the companion
tb by the NN adjacent-swap geometry, so it lies in the triangle
{ta,tb,q}; the same reasoning applies to incoming edges at b.

Thus a first join changes only edges in the block containing f.
Both endpoint restrictions there are trees: the full states are
connected, the block decomposition meets only at articulation
vertices, and the unique cycle is elsewhere. Saturation makes
their envelopes equal to the natural graph on this block, since
every maximal interval in the block is an original strict corner.
Tree connectivity joins the two restrictions. Its flips lift with
all other blocks attached singly, proving that this first join is
internal. This applies to both kinds of first join.

### An outgoing edge on the cycle

Let B select f,r and omit q. Suppose its unique cycle avoids f,r
but has an outgoing edge ad at a, with b<d<c. Transfer ad to bd
by the [general outgoing theorem](COMPONENT_RIGHT_ARM_TRANSFER.md),
giving B'. The companion bd is absent, since otherwise f and r
would lie on the cycle {f,r,ad,bd}. Since f,r were bridges, the
transfer moves one end of the cycle
along a–c–b; the cycle of B' uses both f and r. The
[adjacent-swap theorem](COMPONENT_FOUR_CYCLE_SWAP.md) now gives
B'∼σB'. A second outgoing transfer connects σB' to σB.
Thus B∼σB. The same argument starts with an outgoing cycle edge
at b by reversing the roles of a,b.

For a right first join, the additional held-edge repair is already
covered by the outgoing theorem. Consequently the same-natural-block
cases not covered by this argument have a cycle avoiding a,b, or
meeting one of them only as a sink, with both incident cycle edges
pointing into that vertex.

For example, take area (0,1,2,3,4,5,4), strict corners 05,26, and
a=2,b=3,c=6. A right first join compares representatives

    {01,13,03,05,26,24,34},
    {01,12,02,05,26,24,36}.

Introducing q by 34→23 retaining 24, and then using the middle flip
23→36 retaining 26, takes the first representative to

    B={01,13,03,05,26,24,36}.

Its cycle is {01,13,03}, with b=3 a sink; f=26 and r=36 are
bridges. The second representative has cycle {01,12,02}, with a=2
a sink. Both mixed graphs are acyclic, and the natural graph has
no articulation. The corresponding target flip exchanges 34 with
23 while retaining 24. This is an instance of the remaining
comparison, not a counterexample to component connectivity.
An exact actual-flip search connects these two representatives in
eleven flips. The following additional lemma handles this particular
sink pattern uniformly, but not every sink case.

### A containing edge with the same tail

Suppose the cycle of B avoids f,r and meets a as a sink. Let ta
be an incoming cycle edge. If tv is selected for b<v<c, then
B∼σB.

First, tv is a cover. If an edge is redundant in a unicyclic graph,
its bypass and that edge form the unique cycle, with its head the
only sink. The sink a therefore excludes redundancy of tv, whose
head is v>a.

If ta covers, flip ta→av retaining tv. This creates an outgoing
cycle edge at a, so the preceding adjacent-swap argument applies.
If ta is redundant, write its increasing bypass as

    t=x₀→x₁→...→xₖ=a.

Use the two flips

    tx₁ → x₁v, retaining tv;
    ta → av, retaining tv.

The first breaks the bypass of ta. Its new cycle has two sinks,
a and v, so all its edges cover and the second flip is actual.
Again the endpoint has an outgoing cycle edge av at a.

Both preparations retain f,r, omit q throughout, and exchange only
normal edges properly inside tv. Their adjacent-swap images are
therefore actual source paths. Apply the outgoing-cycle swap at the
prepared state and undo the swapped preparation. This proves B∼σB.
The same argument applies to a sink at b.

In the displayed seven-vertex example, the cycle edge 03 is redundant
and 05 is selected. The preparation is 01→15 retaining 05, followed
by 03→35 retaining 05. Thus the example is covered by this lemma
and the outgoing held-edge repair. The remaining sink cases do not
come with such a selected containing edge at an incoming cycle tail.

## Verification and provenance

Primary derived the forest construction and the existing independent
Astra reviewer audited all three cases, the tree extensions, cover
tests, preservation of F, and the active-middle deduction. Finite
construction checks verify 218 witnesses across all 76 eligible NN
instances through six vertices, and 60 and 45 more in two seven-vertex
fixtures. They check the forests, tree extensions, original-component
membership and actual exposing flips. The two-flip sink preparation
and its adjacent-swap image also pass direct checks.

The separate tool-free Claude consultation reached its monitored
20-minute cap without a final result; none is attributed to it.
No manuscript replacement is made here.

Related Rust: external `nn_component_transport.rs`, mode
`--audit-middle-exposure --construct-exposure`, using the existing
actual-flip model and shared graph API. Sources and receipts are
under `/lake-cache/ai-projects/requests/VerticalStripLLT/middle-exposure/`.

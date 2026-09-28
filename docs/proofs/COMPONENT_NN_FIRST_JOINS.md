# Tree comparisons and incoming bridges in NN joins

2026-09-28. We prove two sufficient criteria for first NN joins to
stay inside an actual component. The second permits a covering edge
of a remote cycle to participate in a tree comparison. It handles
surviving examples where the attached trees alone have different
envelopes. We also prove an incoming-bridge repair whenever a containing
strict covering corner lies anywhere in the selected graph. General
first-join isolation remains open.

## Lifting a tree path through fixed exterior attachments

We work in an ordinary interval-closed natural graph, with its fixed
strict corners. Let W be a set of vertices, with the induced order,
and let T₀,T₁ be trees on W with the same interval envelope H.
Let X be a fixed selected exterior. Suppose X has no directed path
between distinct vertices at which it meets W. Assume T₀∪X is a valid selected state and that every strict
edge not in X is selected in T₀.

**Lemma.** There is an actual flip path from T₀∪X to T₁∪X.

Tree connectivity in H gives a path from T₀ to T₁. Each original
strict edge selected locally is maximal in H, since it is maximal
in the original natural graph. It is therefore retained throughout
the path. Every introduced edge is natural in the original graph:
its interval lies inside a selected local interval.

We check that each local cover test agrees with the full selected
graph. A directed path between local vertices which leaves W must
return through a different attachment vertex; it cannot return to
the same vertex in an ordinary forward graph. Its exterior segment
would thus give a directed path between distinct attachment vertices,
contrary to the hypothesis. No exterior path can destroy a required
local cover. Hence every tree flip lifts, proving the lemma.

The exterior may have any undirected cycle rank and any number of
attachment vertices. With one attachment vertex the directed-path
hypothesis is automatic. In particular, a two-attachment comparison
may be accompanied by further singly attached exterior trees.

## A least incoming tail

We use the saturated ordinary NN notation f=ac, b=a+1, q=ab,
r=bc and σ=(a b). A left first join has representatives

    A=S₀∪σT∪{f,ta,tb},
    D=S₀∪T∪{f,tb,r},                  t<a,

where S₀ consists of the other strict corners and the associated
target flip is actual. Suppose the states are connected and unicyclic,
and their cycle avoids a,b. The cycle is the same at both endpoints:
σ fixes its edges, and the displayed changes occur in attached trees.

Delete the cycle edges. Let Y be the vertex set of the tree containing
a,b,c,t, including its unique root on the cycle. The two restrictions
to Y are trees, and the rest of the state meets Y only at that root.

**Proposition.** If t is the least tail of any selected incoming edge
at a or b, then A and D belong to the same actual component.

The common edge tb contains every incoming edge changed by σ, and
also ta. The common f contains r and every changed outgoing edge:
the NN hypotheses bound all outgoing heads at a,b by c. Thus every
edge present in just one restriction lies inside an edge common to
both. Their interval envelopes on Y are equal. The one-attachment
case of the lemma now connects the full states.

More generally, the same proof works whenever every changed incoming
edge lies inside a common selected interval of the local tree. This
criterion compares the first-join endpoints directly; it does not
require a separate unrestricted incoming-edge transfer theorem.

## Adjoining a covering cycle edge

Suppose the preceding local tree is rooted at one endpoint of a
common cycle edge g=uv, and g covers. Enlarge the local vertex set
to W by including the other endpoint, and adjoin g to each tree.
The enlarged local graphs are still trees. The remaining exterior
meets W only at u,v. It has no directed u-to-v path, since such a
path would make g redundant, and no directed v-to-u path in the
ordinary order.

**Proposition.** If the enlarged local trees have the same envelope
on W, then the first join is internal to an actual component.

Apply the two-attachment lemma. In particular, it suffices that the
common f, tb and g contain all changed edges. The cycle edge g need
not be strict for this argument. If it is strict, it remains selected
throughout the tree path, so every original cycle edge remains fixed.

The same reasoning gives an incoming-bridge repair. Let B select
f,r and omit q, with its unique cycle avoiding f,r. Suppose ta is
a bridge, tb is absent, and Y is the tree component containing
a,b,c,t after the cycle edges are deleted. If a common selected
interval in Y contains ta,tb, tree connectivity in Y proves

    B ∼ B−ta+tb.

If instead such an interval is a covering cycle edge incident to
the root of Y, adjoin that edge and use the two-attachment lemma.
In either case all other selected edges are restored at the endpoint.

## Cutting the cycle at an extremum

Let two connected unicyclic states have the same cycle C. Suppose all
changed edges lie in trees attached at one cycle vertex k. We call z
an extremum of C if its two cycle neighbors are both smaller than z,
or both larger. Choose an extremum z≠k, and remove z together with
all off-cycle trees attached there. The remaining selected graph is a
tree: it contains the path C−z and all trees attached to that path.
The exterior meets it at the two cycle neighbors of z. There is no
directed path between them through z, and the singly attached trees
cannot supply one.

Consequently, if the two remaining trees have equal envelopes, the
first lemma connects the full states. For an incoming-bridge repair
it suffices that a common containing edge g stays in the remaining
tree: the only changed edges ta,tb then lie inside g. In particular,
if g lies on C, any extremum z distinct from k and both endpoints of
g gives the repair. This removes the earlier requirement that g meet k.

The required extremum need not exist. A cycle consisting of two
increasing paths between its minimum and maximum has exactly two
extrema, even if every cycle edge covers. We next handle this case
by moving the attached tree before cutting the cycle.

## A containing strict corner anywhere on the cycle

**Theorem.** Work at a saturated ordinary NN position, with
f=ac, b=a+1, q=ab and r=bc. Let B be connected and unicyclic,
select f,r and omit q. Suppose its unique cycle avoids f,r,
ta is a bridge, and tb is absent, where t<a. If a selected strict
covering cycle edge g contains ta and tb, then

    B ∼ B−ta+tb.

The covering hypothesis is essential. A strict cycle corner may itself
be redundant; the inactive example below does not satisfy the theorem.
If the mixed orientation of the state is acyclic, every strict corner
covers, so the hypothesis only asks that a containing strict corner lie
on the cycle. This condition concerns the state, not merely a component
which has some mixed-acyclic representative.

Write B′=B−ta+tb. The path a–c–b uses bridges. Therefore deleting ta
separates t from both a,b, and B′ has the same unique cycle as B.
After deleting cycle edges, the two endpoints have a common attached
tree vertex set containing t,a,b,c; let k be its root on C.

Every cycle edge covers. Indeed, if a cycle edge were redundant, the
rest of the unique cycle would be an increasing bypass inside its
interval. A different strict cycle edge g cannot lie properly inside
that natural interval, while g itself covers by hypothesis.

If g meets k, use the earlier covering-edge proposition. If an extremum
z avoids k and the endpoints of g, use the preceding cycle cut. Otherwise
C has exactly two extrema: they are k and an endpoint of g. Here we use
that extrema alternate around a cycle and that a covering edge cannot
join the minimum and maximum of a two-extremum cycle. Thus g does not
meet k. The NN conditions on the containing corner give

    g=uv,       u≤t<a<b<v<c.

In this exceptional configuration t,a,b lie strictly between the two
cycle extrema. For t this also uses that it is not on the cycle:
otherwise ta would attach the a,b,c-side at t, making k=t.

We will first arrange a common bridge kx such that x lies strictly
between the extrema and every changed edge lies on its x-side. There
are two cases, according to which side of ta contains C.

**The cycle is on the t-side.** Remove the a,b,c-side and all cycle
edges. The common tree joining k to t can be normalized so that its
k–t path stays in the interval between k and t, by the
[interval-path lemma](COMPONENT_TREE_CONNECTIVITY.md). Apply the same
normalizing flips to both endpoints. They lift: the exterior cycle
attaches only at k, and the removed tree attaches only at t, with no
exterior connection between these vertices. The first edge kx of the
normalized path separates all differences and has the required order.

**The cycle is on the a,b,c-side.** Remove the pendant t-side tree and
all cycle edges. Let R be the common tree containing k,a,b,c, and put
H=Env(R). Its maximal intervals M form increasing chains. The edge q
is properly inside the selected f, so q∉M; since a,b are adjacent,
they lie in different M-chains. Thus F=M∪{q} is a forest.

We construct a tree R* with envelope H, containing q, whose path from
k to {a,b} stays in

    I=[min(k,a),max(k,b)]∩V(R).

Each component of F meets I in a connected subtree, when the
intersection is nonempty. For the ordinary components this is the
intersection of an increasing chain with an interval. The exceptional
component consists of two such chains joined by q, and both endpoints
of q lie in I. The induced graph H[I] is connected. Contract these
intersections, choose a simple path from the class of k to the class
containing q, and lift its edges together with F. This is a forest;
extend it to a spanning tree R* of H. If k already belongs to the
q-component, no quotient-path edges are needed. Its existing F-path
to q lies in I.

Tree connectivity normalizes R to R*. These common flips lift in both
endpoints: the cycle meets R only at k, while the pendant tree meets
it only at a or b, respectively. These exterior pieces are disconnected.
All original strict edges remain selected because they are maximal in H.
The first edge kx on the path to q separates both a,b from k. Since I
lies between the two cycle extrema, x has the required order. We do not
require q or r to stay selected during the normalizing path.

Now let j be either cycle neighbor of k. By reversing the order for
this comparison if necessary, write k<x and k<j. The following two
moves apply according to the order of x,j:

| Order | Retained edge | Exchanged edges | Effect |
| --- | --- | --- | --- |
| k<x<j | kj | kx → xj | Move the attached tree to j. |
| k<j<x | kx | kj → jx | Include x in the cycle. |

Both are actual flips in both endpoints. In the first row the exchanged
edge remains a bridge and the cycle is unchanged. In the second row
the old retained edge is a bridge; an alternate directed path making
it redundant after the flip would give an alternate directed k–j path
beforehand, contrary to kj covering. The new short edge covers as well.
The exchanged edge is a proper subinterval of the retained natural
edge, so it is not strict. The corner g is untouched.

After either move k is still a cycle extremum, but the differing tree
is attached at a different vertex. All differences remain ta versus tb,
and g is not incident to k. Cut the cycle at k. The remaining trees
have equal envelopes: their only changed intervals lie inside the
common g. The first lemma joins them. Undo the preparation made in B′
to obtain B∼B′, proving the theorem.

This resolves the case where the containing corner is on the cycle.
We now treat a corner in a different attached tree.

## A containing corner in a different attached tree

**Theorem.** Keep the preceding NN hypotheses on B,f,r,q,ta,tb, but
allow the selected strict covering container g of ta,tb to lie anywhere
in B. Then B∼B−ta+tb.

If g lies in the attached tree containing t,a,b,c, that tree and its
modified endpoint have equal envelopes, since g contains the changed
edges. The one-attachment lemma applies. If g lies on the cycle, apply
the preceding theorem. It remains to consider a tree containing g
attached at a different cycle vertex l≠k.

If C has an extremum distinct from k,l, cut there. The remaining trees
contain g and all changed edges, so their envelopes agree. Otherwise
C has exactly two extrema, k and l. At either root we can choose an
incident covering cycle edge: a unicycle has at most one redundant
edge. That redundant edge, if present, need not be normal; the argument
only requires that the chosen incident edge cover.

Call a label inward from k if it is strictly on the side of k containing
l, and outward if it is strictly on the opposite side. We first try the
common normalizations from the preceding theorem. When the cycle lies
on the t-side, this works if t is inward. When it lies on the a,b,c-side,
it works if both a,b are inward. Their construction puts the first
common bridge kx inward, with all differences on its x-side. It does
not require x to stop before l. Compare kx with an incident covering
cycle edge kj, and use the same slide or expansion. The old k remains
an extremum while the differing tree moves away from k. Cutting at k
retains g, which is in the tree attached at l, and gives equal envelopes.

In every other case g has an endpoint w outward from k. To check the
boundary cases, write g=uv with u≤t<a<b<v<c. If the cycle is on the
t-side and t=k is the minimum, then u<k: equality would make g incident
to the wrong cycle root. If k is the maximum, v>b>t=k. If the cycle is
on the core side and one of a,b is equal to k or outward, the strict
inequalities u<a and b<v give an outward endpoint. The remaining cases
follow directly from g containing t,a,b.

This w is inward from the opposite root l. Normalize the common tree
containing g so that its l–w path stays in the interval between l and w.
All original strict edges, including g, remain selected. The common
normalizing flips lift because the rest of the graph attaches only at l.
Let lx be the first edge of this path. The edge g lies on the x-side
unless lx=g: if the path uses g, that edge occurs at or after the first
step; if not, it is attached at w on that same side of lx.

Compare lx with an incident covering cycle edge lj. A slide or expansion
again moves the tree past l. If lx≠g, the old l is now an extremum where
we may cut: g and the changed tree at k both remain in the local tree,
so their envelopes agree. If lx=g, a slide is impossible, because it
would place the strict g properly inside the retained natural lj.
The expansion instead makes g a covering cycle edge. The other attached
trees are unchanged, so f,r remain bridges. Apply the cycle-corner
theorem, and then undo the common preparation. This proves the claim.

**Corollary.** In a connected unicyclic saturated NN state selecting
f,r and omitting q, an incoming bridge ta with tb absent can be moved
to tb whenever the state has an acyclic mixed orientation.

Saturation supplies a strict container of ta. The NN conditions ensure
that it also contains tb, and mixed acyclicity makes it a cover. If the
cycle avoids f,r, apply the theorem just proved. If it uses either edge,
apply the earlier
[incoming-bridge corollary](COMPONENT_FOUR_CYCLE_SWAP.md#transferring-a-single-incoming-bridge).
This is a statement about an individual state with the stated hypotheses;
we have not proved that every recurrence join has such a representative.

## First joins whose cycle avoids the adjacent vertices

**Corollary.** Suppose B selects f,r, omits q, is connected and unicyclic,
and its cycle avoids a,b. If its mixed orientation is acyclic, then
B∼σB, where σ=(a b).

Every changed edge incident to a or b is a bridge. No pair ta,tb can
both be selected, since together with f,r it would give a cycle through
a,b; the same holds for a pair ad,bd. Move the incoming bridges one at
a time by the preceding corollary, and the outgoing bridges by the
[outgoing-edge theorem](COMPONENT_RIGHT_ARM_TRANSFER.md). For an incoming
edge initially at b, apply the corollary to the proposed endpoint and
reverse its path; that endpoint is another mixed-acyclic unicycle with
the same cycle. Each endpoint
operation restores every other edge and leaves the original cycle
unchanged. Thus the mixed orientation remains acyclic at the endpoints,
which supplies the hypothesis for each subsequent incoming move.
The edges f,r remain selected, q remains absent at these endpoints,
and the final state is σB.

**Corollary.** A left or right first NN join is internal if its first
representative is connected, unicyclic, has an acyclic mixed orientation,
and its cycle avoids a,b.

For the left join, start with

    A=S₀∪σT∪{f,ta,tb}.

Exchange ta with q retaining tb, and then exchange q with r retaining f.
These are actual flips of bridges, since the cycle avoids a,b. They give
B=S₀∪σT∪{f,tb,r}, with the same mixed-acyclic cycle. The preceding
corollary connects this to σB=S₀∪T∪{f,ta,r}. An incoming-bridge repair
then gives the required endpoint D=S₀∪T∪{f,tb,r}.

For a right join, start with A=S₀∪σT∪{f,ad,bd}. Exchange bd with q
retaining ad, and then q with r retaining f. Apply the swap corollary
to the resulting B=S₀∪σT∪{f,ad,r}. Its image is S₀∪T∪{f,bd,r};
the outgoing transfer bd→ad gives the required endpoint. Again all
preparations leave the unique cycle unchanged.

This settles the remote-cycle first joins at mixed-acyclic representatives.
First joins with the cycle meeting a or b as a sink, and the passage from
these state hypotheses to all relevant component pieces, remain.

## A first join with a smaller exterior tail

The least-tail condition is not automatic, even for surviving states.
Take area (0,1,2,3,4,5,6,7,4,5), with strict corners 07,49, and
use a=4,b=5,c=9,t=2. Put

    Z={07,06,36,37,79,89}.

The two representatives

    A=Z∪{15,49,24,25},
    D=Z∪{14,49,25,59}

form a left first join. The target state
Z∪{14,24,25,59} has the actual flip 24→45 retaining 25.
Both source states have the unique cycle 0–6–3–7–0. Reversing
the strict corner 07 gives 7→0→6←3→7, so both mixed graphs
are acyclic; the other strict edge 49 is a bridge.

The attached tree has vertex set {1,2,4,5,7,8,9} and root 7.
Its maximal intervals are {15,49} for A and {14,25,49} for D.
Thus tree flips confined to this vertex set cannot connect the
restrictions. This does not obstruct the covering-edge criterion:
adjoin the covering strict edge 07 and vertex 0. Both enlarged
trees have maximal intervals {07,49}. Their exterior is the path

    0→6←3→7,

which has no directed path between 0 and 7. The proposition therefore
connects A and D while retaining every cycle edge.

## Why the covering hypothesis matters

There is an analogous surviving incoming-bridge example on nine
vertices, with area (0,1,2,3,4,5,6,4,5), strict corners 06,38,
and a=3,b=4,c=8. Let

    B={06,05,25,26,13,38,48,68,78}.

The unique cycle is 0–5–2–6–0, and 06 covers. The attached tree
containing f has maximal intervals {13,38}; replacing 13 by 14
changes them to {14,38}. Adjoining 06 makes both enlarged envelopes
have maximal intervals {06,38}. The exterior path 0→5←2→6 has
no directed connection between its endpoints, so the repair is valid.

By contrast, the earlier inactive example has cycle {06,02,26}.
Its exterior contains 0→2→6. The local tree regards 06 as a
cover, whereas the full state does not. The lifting hypothesis
therefore fails, in agreement with the
[incoming-transfer obstruction](COMPONENT_RIGHT_ARM_TRANSFER.md).

## Scope and verification

The two-attachment lemma is independent of the exterior cycle rank.
Its NN applications here require the specified attached trees and
covering edge; survival alone has not been shown to supply them.
The incoming-bridge theorem now permits a strict covering container
anywhere in the graph. It does not automatically compare all changed
incoming edges of a first join, or supply a covering container at every
representative in a component. General first joins, DN/DD, recurrence coverage and higher cycle ranks remain
part of the ordinary component-proof goal.

Primary and the existing Astra reviewer independently checked the
criteria and their proofs. Exact local tree searches give an eleven-flip
path for the ten-vertex first join and a ten-flip path for the nine-vertex
bridge repair. Every traversed local flip lifts in the original full
diagram: 12,109 and 1,665 checks, respectively. The inactive example
fails the cover test as stated. Correct local-envelope maxima were
also checked explicitly.

Related Rust: external `first_join_tree_lifts.rs`, reusing the existing
actual-flip model. Sources and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/first-join-tree-lifts/`.
No Lean or manuscript source changed.

A subsequent exact run checks a nonincident cycle corner, two common
bridge preparations, and both orientations of the bridge in the theorem.
The latter checks include a cycle expansion, and the q-normalization
when the core root is c. Local paths have 12,13,10,6,8 flips, respectively;
all 29,936,16,692,60,622,2,983,2,536 traversed local flips agree with the
full diagram and preserve every original strict corner. The four paired
preparations have 2,1,1,2 flips per endpoint and are also checked directly.
Primary and the existing Astra reviewer independently audited the general
argument, including the case where k already lies in the q-component.
Sources and receipts for this extension are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/cycle-path-tree-lifts/`.

The different-tree extension has three further exact fixtures: an inward
common connector, an outward containing tree, and a strict containing
edge which enters the cycle. Their local paths have 14,15,15 flips and
83,883,77,887,37,451 local/global cover comparisons. Each has one common
preparation flip per endpoint. These use the same frozen consumer and
receipt directory. The written proof is separate from these finite checks.

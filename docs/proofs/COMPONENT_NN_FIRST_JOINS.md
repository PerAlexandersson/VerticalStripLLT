# Tree comparisons for first NN joins

2026-09-28. We prove two sufficient criteria for first NN joins to
stay inside an actual component. The second permits a covering edge
of a remote cycle to participate in a tree comparison. It handles
surviving examples where the attached trees alone have different
envelopes. General first-join isolation remains open.

## Lifting a tree path through two attachment vertices

We work in an ordinary interval-closed natural graph, with its fixed
strict corners. Let W be a set of vertices, with the induced order,
and let T₀,T₁ be trees on W with the same interval envelope H.
Let X be a fixed selected exterior. Suppose X meets W at at most
two vertices u,v and has no directed path between distinct attachment
vertices. Assume T₀∪X is a valid selected state and that every strict
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

The exterior may have any undirected cycle rank. With one attachment
vertex the directed-path hypothesis is automatic.

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
In particular, a covering cycle edge containing the relevant incoming
edges need not already meet the root of the attached tree. General
first joins, DN/DD, recurrence coverage and higher cycle ranks remain
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

# Repairing NN pieces at a sink

2026-09-28. In pushing a component through the NN recurrence, an adjacent
swap can leave a piece whose unique cycle meets a or b only through two
incoming edges. We prove the swap repair for this configuration. This is
one repair used in the recurrence bookkeeping, not a replacement for that
bookkeeping or a proof of the full component formula.

## The repair

Keep the saturated ordinary NN hypotheses, with b=a+1, strict corner
f=ac, r=bc and q=ab. Write σ=(a b). Let B be connected and unicyclic,
select f,r and omit q. Suppose its cycle avoids f,r and meets a or b
as a sink.

**Theorem.** B and σB belong to the same actual component.

It suffices to prove the assertion when a is the sink: otherwise apply
that assertion to the valid state σB. Saturation supplies a strict
corner g=uv containing one incoming cycle edge ta. The NN hypotheses give

    u≤t<a<b<v<c.

We prepare an outgoing cycle edge at a, apply the already proved
[outgoing-cycle swap](COMPONENT_NN_MIDDLE_JOINS.md#an-outgoing-edge-on-the-cycle),
and undo the swapped preparation. Except for one explicitly paired
bridge transfer, all preparations omit q and retain f,r. Their σ-images
are therefore valid source paths. The paired transfer will have its
own connection between swapped endpoints.

## Comparing trees after a cycle cut

Choose a cycle extremum z: both its cycle neighbors are larger than z,
or both are smaller. Remove z and all trees attached there. The remaining
graph is a tree. The fixed exterior connects its two cycle attachment
vertices through z, but has no directed path between them. We may also
freeze the entire tree attached through f, including r and b, outside
our local tree; it meets the local tree only at a.

The [tree-lifting lemma](COMPONENT_NN_FIRST_JOINS.md) applies with these
several attachment vertices. Thus two local trees with equal envelopes
are connected while the exterior stays fixed. The local vertices omit b,
so this path omits q.

We use this when a selected cycle edge e lies inside g and the local
a–v path uses e. Replacing e by av is then another local tree with the
same envelope: both exchanged intervals lie inside the retained g.
Restoring the exterior gives a cycle containing the outgoing edge av.
This proves the required preparation whenever such a cut is available.

## The containing corner is on the cycle

Split the cycle into its two a–v arcs P₁,P₂, with P₁ ending in g.
Let sa be the edge of P₁ at a.

If s≥u, choose e=sa, which lies inside g. The other arc P₂ starts
below a and ends at v>a, so it has an internal minimum z<a. This vertex
avoids e and both endpoints of g. Cutting there leaves P₁ as the local
a–v path, and the preceding comparison applies.

If s<u, the given contained edge ta lies on P₂. A minimum z of P₁
satisfies z≤s<u and is internal. It avoids g and ta. Cutting there
leaves P₂ as the local a–v path. Use e=ta in the same comparison.

This handles every on-cycle placement of g.

## Putting an off-cycle corner in its own branch

The edges f,r are bridges. Removing them separates the trees attached
through b and c from a and the cycle. We first ensure that the branch
containing g contains neither b nor c.

If g lies in the b-tree, normalize its b–u path inside [u,b] by the
[interval-path lemma](COMPONENT_TREE_CONNECTIVITY.md). Its first edge xb
has u≤x<a, and g lies beyond it. The selected strict bridge g contains
both xa and xb. The
[incoming-bridge theorem](COMPONENT_NN_FIRST_JOINS.md#a-containing-corner-in-a-different-attached-tree)
therefore moves this whole branch from b to a. For the swapped state,
use a separate application of the same theorem to move the corresponding
branch from a to b. We do not conjugate the interior of this macro path,
which may contain q. The endpoint connections suffice.

If g lies in the c-tree, normalize its c–v path inside [v,c]. The
first edge xc has b<v≤x<c. Exchange xc with ax, retaining f; this is
an actual bridge flip. Its swapped counterpart exchanges xc with bx,
retaining r. We now have a g-branch at a containing neither b nor c.
The normalizing paths preserve all strict edges and lift because their
exteriors meet them only at the root.

If the g-branch is rooted at a, normalize its a–u path inside [u,a].
Its first edge xa has u≤x<a, and g lies beyond it. Choose an incoming
cycle edge t₀a which covers; at least one of the two does, because a
unicycle has at most one redundant edge. Use the appropriate move:

| Order | Retained edge | Exchanged edges |
| --- | --- | --- |
| t₀<x<a | t₀a | xa → t₀x |
| x<t₀<a | xa | t₀a → xt₀ |

The first moves the branch to t₀; the second expands the cycle through
x. Both moves are actual, by the bridge slide/expansion cover check in
the incoming-bridge proof. The edge exchanged is properly inside its
retained edge, so it is not strict. The sink remains a, and the corner
g is now in a branch rooted at a different cycle vertex. There is still
a contained incoming cycle edge: in the first row the cycle is unchanged;
in the second, the new xa lies inside g.

We have reduced to a g-branch rooted at l≠a, excluding b,c. All the
remaining normalizations take place in this branch and omit q.

## A corner attached at a different cycle vertex

Let P₁ be the a–l arc starting with a contained incoming edge ta,
and P₂ the other arc, starting with sa.

If P₂ has an internal extremum, cut there and use e=ta. The local
a–v path follows P₁ and then the attached tree. If P₂ has no internal
extremum, it is strictly decreasing from a to l. If s≥u and P₁ has
an internal extremum, cut on P₁ instead and use e=sa, also inside g.
There are two remaining cases.

**Both arcs are monotone.** The cycle extrema are l and a. Choose a
contained incoming edge e whose a–l arc has at least two edges. Such
an edge exists: use ta unless t=l; in that case the other incoming
edge sa is also contained in g, since s>l≥u. Let j be the neighbor
of l along the chosen arc. Then j≠a and lj covers.

Normalize the branch's l–v path inside [l,v], and let lx be its first
edge. Here x>l. Compare it with lj:

| Order | Retained edge | Exchanged edges |
| --- | --- | --- |
| l<x<j | lj | lx → xj |
| l<j<x | lx | lj → jx |

If lx=g, strictness rules out the first row; the second puts g on the
cycle, reducing to the on-cycle case. Otherwise g moves away from l,
which remains a cycle minimum. Cut at l. The local a–v path uses the
chosen e, so replacing e by av finishes the preparation.

**P₂ is decreasing, s<u, and P₁ is not monotone.** In this case ta
covers. If it were redundant, the remaining cycle would be an increasing
t-to-a bypass, contradicting the cycle vertex s<t.

Normalize the branch's l–u path inside [l,u]. Its first edge lx satisfies
l<x≤u. Let j be the next vertex towards a along P₂. The edge lj covers.
For j≠a, redundancy would make j the unique cycle sink, contrary to
the sink a. For j=a, redundancy would force the complementary path to
be increasing, and in particular P₁ to be monotone, contrary to this case.

If j<x, exchange lj with jx retaining lx. The vertex j becomes a cycle
minimum: its two neighbors, x and the next vertex on P₂, are larger.
Cut at j. The local a–v path now uses P₁ and ta, so replace ta by av.

If x<j, exchange lx with xj retaining lj. This moves the branch one
vertex nearer a along P₂. For j<a we still have j≤s<u, and we repeat.
The number of edges remaining on this fixed arc decreases at each slide.

If a slide reaches a, normalize the a–u path inside [u,a], with first
edge ya and u≤y<a. Compare it with the covering ta. For t<y, the
slide ya→ty retaining ta attaches the branch at t. For y<t, the
expansion ta→yt retaining ya attaches it at y. In either case the new
root is at least u, and the incoming edge at a on that side is contained
in g. The opposite arc starts at s<u, so it has an internal minimum
below u. Cutting there permits the same replacement by av.

Every branch normalization and local comparison preserves strict edges.
All exchanged intervals in the displayed moves are inside retained
natural intervals. All paths here omit q and retain f,r. We have thus
prepared an outgoing cycle edge at a in every case. Applying the
outgoing-cycle swap, then undoing the swapped preparations (and the
separately paired b-branch transfer if used), proves the theorem.

## Role in the component recurrence

This supplies the sink swap needed when repairing a first NN piece.
It does not by itself identify all smaller components, supply the final
held-edge repair in every first join, or handle higher cycle ranks.
The direct starting point remains the one-component coefficient formula
in [NN redistribution](COMPONENT_NN_REDISTRIBUTION.md); further repairs
must be applied to those coefficients and checked across target flips.

Primary and the existing independent Astra reviewer audited the case
split, cover checks and final written proof. The final audit passed.
The complete-component scan checks both sink positions in all 76 eligible
NN instances through six vertices, with counts [2,2]. The seven-vertex
area (0,1,2,3,4,3,2) adds [2,2]; the three-corner fixture has no such
states. Exact local comparisons on 8,11,10 vertices give paths of 3,5,5
flips and 36,170,341 local/global cover checks. They cover both cycle-arc
choices and a corner in another attached tree. Their local vertices omit
b, and every displayed state omits q. These finite checks support the
proof; they do not verify every branch-normalization construction.
Related Rust: external `nn_component_transport.rs --audit-sink-swap`,
using the existing complete-component index and actual cover-flip model.
Receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/sink-recurrence-repair/`.
No Lean or manuscript source has changed.

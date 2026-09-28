# Swapping attachments of an ordinary four-cycle

2026-09-28. This is a mathematical proof, independently audited by Astra
and primary. It resolves both second mixed NN joins in cycle rank
one, and gives a swap theorem for longer unicyclic states. Claude
also audited the reduction to a four-cycle; primary and Astra checked
the shorter final version. The full
component recurrence, its other joins and higher cycle
ranks remain open. No Lean implementation is claimed here.

## Setting and statement

We use a saturated ordinary NN diagram with strict corner f=ac,
b=a+1, and adjacent swap σ=(a b). We retain the full NN hypotheses
from [the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md). In particular,
neither a nor b is a strict head, every natural edge leaving a or b
ends at or before c, and σ preserves the exterior natural edges and
the other strict corners.

**Theorem.** Suppose a connected unicyclic selected state A contains

    {ac,ad,bd,bc},       a<b<d<c.

Then A and σA belong to the same actual flip component.

The displayed four-cycle is the unique cycle. Every remaining edge
belongs to a tree attached at exactly one of its vertices. A branch
below means a component after deleting the four core vertices, together
with its unique attachment edge. Swapping a,b changes only the
attachments of branches rooted at a or b; the four-cycle itself is fixed
as a set.

We will move these branches one at a time. A tree attached at a single
vertex does not change cover tests among the other vertices: a simple
path cannot enter that tree and return to the same attachment vertex.
Thus each local flip below lifts in the presence of all the other
branches. More generally, tree-normalizing flips inside one branch
together with its root lift for the same reason.

## Three local moves

An outgoing attachment ax, with b<x<c, can be transferred to b by

    ax → xc, retaining ac;
    xc → bx, retaining bc.

The attachment remains a bridge and the core covers remain covers.
Both flips are actual. Reversing them transfers an outgoing branch
from b to a.

Next suppose the core also has a bridge dz with b<d<z<c. We can move
the cycle from d to z by the following seven flips.

| Retained edge | Exchanged edges |
| --- | --- |
| ac | ad → dc |
| dc | dz → zc |
| ac | dc → ad |
| ac | zc → az |
| ad | bd → ab |
| az | ab → bz |
| az | ad → dz |

The final edges are {ac,az,bz,bc,dz}. All required cover tests hold.
The only temporary redundant edges in this local graph are bc after
the first two steps and ac after the fifth; neither is used as a
required cover then. Reversing the table handles b<z<d<c.

We can also move the cycle to an interior vertex z attached to any
other core vertex. First transfer its attachment to a, using the
outgoing moves above if it is at b or c. If z>d, the last three rows
of the table move the cycle to z. If z<d, first replace az by zd,
retaining ad, and then use the reversed seven-step move. Hence the
cycle can move successively along any selected branch path whose
noncore vertices lie in (b,c).

Finally, suppose we have a selected strict edge ud and an incoming
attachment xa, with

    u<x<a<b<d<c.

The following six flips transfer xa to xb and restore the core and ud.

| Retained edge | Exchanged edges |
| --- | --- |
| ud | ad → ua |
| ua | xa → ux |
| ud | ua → ad |
| ud | bd → ub |
| ub | ux → xb |
| ud | ub → bd |

Each local intermediate graph has one cycle and every selected edge
covers. Every new edge lies inside its retained natural interval, and
no strict edge is exchanged. Thus the table gives actual source flips.
It remains valid with arbitrary singly attached exterior trees.

## An incoming branch with a shield in the same tree

Consider an incoming attachment xa, x<a. Since the diagram is saturated,
some selected strict interval uv contains xa. The NN hypotheses give

    u≤x<a<b<v<c.

Indeed its head cannot be a or b; if v≥c it would contain f, contrary
to maximality. Call uv the chosen containing corner.

Suppose uv belongs to the branch containing x. On this branch together
with root a, replace the attachment xa by av. The remaining branch
edges are unchanged. Both graphs are trees with the same envelope:
xa and av both lie inside the selected interval uv. Tree connectivity
therefore supplies actual flips between them. These flips lift with
the rest of A attached at a, and retain all original strict corners.

Transfer av to bv by the two outgoing flips. Now reverse the
σ-conjugate of the tree-normalizing path. The result is the original
branch with attachment xb. Conjugation is order preserving on this
branch's vertex set, which contains only one of a,b, and preserves
its natural edges and strict corners by the NN hypotheses.

## A containing corner in a different tree

Suppose instead that uv belongs to another branch, rooted at a core
vertex k. Apply
[the interval-path lemma](COMPONENT_TREE_CONNECTIVITY.md) to that branch
together with k. We may arrange its k–v path entirely inside the
interval between k and v. Every noncore vertex of this path lies in
(b,c). The normalization retains uv because it is maximal in the
branch envelope, and lifts with the rest of A attached at k.

Move the cycle along this path using the local moves above. We obtain
the core {ac,av,bv,bc}, while uv and the branch attached by xa remain
untouched. If v was already the core vertex d, this path is empty and
no normalization or migration is needed.

The two branches are distinct, so u≠x and hence u<x. We can now apply
the six-flip table with d replaced by v. It transfers xa to xb while
restoring the migrated core and uv. Undo the cycle migration and the
tree normalization. The transferred branch is attached only at b,
so it cannot obstruct any of these reversed cover tests.

We have transferred one incoming branch and restored every other edge.
The reverse construction transfers a branch from b to a. Together with
the outgoing moves, this handles every original branch rooted at a or b.
Performing these transfers one at a time yields σA, proving the theorem.

## The left four-cycle

**Theorem.** In the same NN setting, suppose a connected unicyclic
selected state A contains

    {ta,tb,ac,bc},       t<a<b<c.

Then A and σA belong to the same actual flip component.

Again the displayed cycle is unique, and we transfer its attached
branches one at a time. Outgoing attachments at a,b use the same
two flips through c as before. An incoming attachment xa with t<x<a
can be transferred by

    xa → tx, retaining ta;
    tx → xb, retaining tb.

Thus we only need an incoming attachment with x<t. Choose a containing
strict corner uv. As before, the NN hypotheses give

    u≤x<t<a<b<v<c.

If uv lies in the branch containing x, use the same-branch tree
normalization and outgoing transfer already proved above.

Suppose it lies in another branch, rooted at k∈{t,a,b,c}. First take
k=t,a, or b. In the branch together with its root, let M be the maximal
intervals of the tree envelope. They contain uv. Since u<k<v, the
vertex k cannot belong to the increasing M-chain containing the edge
uv. The graph M∪{kv} is therefore a forest, and kv is natural because
it lies inside uv. Extend this forest to a spanning tree of the same
envelope. Tree connectivity gives a normalization with kv selected,
while retaining uv and every original strict edge. As always, it
lifts to the whole state because this tree meets the rest only at k.

For k=t, the following two flips convert the left core to the right
core at v, retaining the bridge tv:

    ta → av, retaining tv;
    tb → bv, retaining tv.

For k=a, use instead

    ta → ab, retaining tb;
    ab → bv, retaining av.

The result has right core {ac,av,bv,bc}, with t attached by tb.
If k=b, first transfer the bridge bv to av through c, then use this
second conversion. Both conversions are actual: all local edges cover,
except that ac is temporarily redundant after introducing ab. That
edge is not used in the next cover test. No strict edge is exchanged.

Finally, suppose k=c. Normalize the c–v path inside [v,c] by the
interval-path lemma. Let z be its first vertex after c. Replace zc
by az, retaining ac, and use the second conversion above with z in
place of v. We now have a right core at z. Move that core along the
remaining path to v by the already proved right-hand mobility. All
its vertices are in (b,c), and the crossing strict corner uv is
untouched.

In all cases we have obtained the right core at v, while preserving
uv and the branch attached by xa. Distinct branches give u<x. Apply
the six-flip table to this one branch, transferring xa to xb, then
undo the conversion, migration and normalization. Its new attachment
at b cannot change cover tests in the other branches.

This transfers every incoming branch, with all other edges restored.
Reversing the construction handles attachments at b. Combining these
transfers proves the theorem. We undo the original moves after a
single branch transfer; we do not conjugate intermediate states that
may contain ab.

## Reduction of a unicyclic state to a four-cycle

**Theorem.** Suppose a connected unicyclic selected state A contains
f=ac and r=bc, omits q=ab, and f lies on its unique cycle. Then A and
σA belong to the same actual flip component.

We delete f and normalize the remaining tree toward a tree containing q.
Immediately before the first introduction of q, we have one of the
two four-cycles. The preceding path admits the adjacent swap.

Delete f from A, leaving a spanning tree T. Write H for its envelope
and M for the maximal intervals of H. The edge f does not belong to H:
any selected interval containing f would contradict its maximality in
the original diagram. Moreover, r is maximal in H. A larger interval
containing r either begins at or before a and contains f, or begins
at b and ends beyond c, contrary to the NN hypotheses. Thus r∈M.

The edges of M form disjoint increasing chains. The vertices a and b
belong to different chains, since an increasing path between adjacent
vertices would require q∈M⊆T. Since r∈M, the same holds for a and c.

Connectedness of H implies q∈H: an edge crossing the cut between the
adjacent vertices a,b contains q. Since a,b lie in different M-chains,
M∪{q} is a forest. Extend it to a spanning tree T′ of H. This tree
contains M and has envelope H.

Tree connectivity gives a path from T to T′ retaining M. Reinsert f
at every step. This cannot destroy a cover test for another edge: a
directed path using f could bypass an edge xy only if [x,y] contains
[a,c], impossible for another natural edge. All original strict
corners other than f belong to M and remain selected. We therefore
obtain an actual source path from A to T′∪{f}.

The endpoint contains q. We stop at the state P immediately before
its first occurrence. A flip introducing q must retain either tb,
exchanging ta with q for t<a, or ad, exchanging bd with q for d>b.
The latter has d<c, since f∉H. Since f,r remain selected, P already
contains the corresponding four-cycle. The flip cannot retain f,
which is absent from every tree on the path. Since P is still a tree
plus f, the displayed four-cycle is its unique cycle.

The path from A to P omits q throughout and retains f,r. No flip
triple contains both a,b, since such a flip would exchange q. Thus
σ preserves the order on every flip triple. It also preserves the
directed graph of each state, hence the required cover tests. The
two edges f,r are interchanged but never removed, and every other
strict corner is fixed. The σ-image of the path is consequently a
valid source path from σA to σP. Apply the appropriate four-cycle
theorem to connect P to σP, then reverse this image path. This proves
the claim.

**Corollary.** The same conclusion holds if r, rather than f, lies on
the unique cycle. Thus it suffices that the cycle uses at least one
of f,r.

Indeed, σA is another valid source state with f,r selected and q absent.
The cycle of σA contains f, so the theorem applied to σA gives the claim.

## Application to the NN packet joins

For a right target flip, write its exterior states as

    Q=T∪{ad,bd},       P=T∪{ad},       a<b<d<c.

The second mixed source join compares

    S₀∪σT∪{ac,ad,bd,bc},
    S₀∪T∪{ac,ad,ab,bc},

where S₀ contains the other strict edges. The target flip lifts to
the source by adding the redundant ac: exchanging ab with bd and
retaining ad gives S₀∪T∪{ac,ad,bd,bc}. The theorem connects this to
the first state. Thus this packet generator does not join distinct
connected unicyclic source components.

For a left target flip, write Q=T∪{ta,tb} and P=T∪{tb}, where
t<a<b<c. The corresponding second mixed join compares

    S₀∪σT∪{ac,ta,tb,bc},
    S₀∪T∪{ac,tb,ab,bc}.

Adding redundant ac lifts the target flip that exchanges ab with ta,
retaining tb. The resulting state has the left four-cycle, and the
left theorem finishes the comparison. Thus neither kind of second
mixed NN join identifies distinct connected unicyclic components.

We do not claim the same conclusion yet for the surviving endpoints
of middle or first mixed joins, or for components with more than one cycle.
For example, a right first mixed join compares

    S₀∪σT∪{f,ad,bd},       S₀∪T∪{f,ad,r}.

Flipping bd to q in the first state and taking its middle partner
gives S₀∪σT∪{f,ad,r}. Even if the general swap theorem applies, its
image is S₀∪T∪{f,bd,r}, with bd where the required endpoint has ad.
Thus the swap theorem alone does not prove this first mixed join.

There is nevertheless a consequence for every middle join that is not
an actual flip. Its 10 endpoint has f redundant, since q always covers.
The unique cycle therefore contains f. Replacing q by r leaves this
cycle if q was a bridge; if q was on the cycle, the new unique cycle
contains r. The corollary applies to the 01 endpoint in both cases.
Hence that endpoint and its full σ-image belong to the same source
component. This does not yet connect it to the 10 endpoint.

## Checks and a restriction to avoid

The explicit six- and seven-flip tables were found using the existing
Rust actual-cover model and then verified mathematically. An exhaustive
check over all 76 eligible NN instances through six vertices verifies
the right theorem on all 149 connected unicyclic states containing its
four-cycle. These are checks of actual component membership,
not comparisons of polynomial values. The seven-vertex fixtures
area0123434 and area0123343 check another 44 and 13 such states.
The left theorem passes the same scan on 24 states and the two fixtures
on 47 and 5 states. The two left-to-right conversion tables also pass
direct checks in the actual-cover model. The general swap theorem with
f on the cycle passes on 519 states in the same six-vertex scan, and
on 257 and 72 states in the two seven-vertex fixtures.

One cannot instead delete bc after making it redundant and appeal to
tree connectivity while insisting that b still reaches c. Even the
special pair above can lie in different restricted tree components.
In K5, with f=04 and r=14, take

    A={04,03,13,14,02},       σA={04,03,13,14,12}.

After replacing 03 by 34 and deleting 14, the two trees have restricted
components

    {{04,13,34,02}, {04,13,34,24}},
    {{04,13,34,12}, {04,13,34,23}},

among trees omitting 14 and retaining a directed 1→4 path. Their path
1→3→4 is even identical. The original states are nevertheless joined
by the two outgoing flips 02→24→12. The proof above allows temporary
changes in which edges are redundant.

Related Rust: `nn_component_transport.rs`, modes `--shield-swap-path`,
`--cycle-slide`, `--audit-four-cycle`, and the exact restricted-tree
counterexample mode. Frozen sources, Cargo files,
commands, receipts and hashes are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/four-cycle-attachment/`.
The left conversions, left theorem and general unicyclic swap use the
additional modes `--cycle-cross`, `--cycle-from-a`,
`--audit-left-four-cycle` and `--audit-unicyclic-swap`. Their frozen
consumer, commands and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/left-four-cycle/`.
The shared Rust sources and the Lean/manuscript sources were not changed.

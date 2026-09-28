# Swapping attachments of an ordinary four-cycle

2026-09-28. This is a mathematical proof, independently audited by Astra
and primary. It resolves the right second mixed NN join in cycle rank
one. The full component recurrence, its other joins and higher cycle
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

## Application to the NN packet join

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

We do not claim the same conclusion yet for the left second mixed
join, the surviving endpoints of middle or first mixed joins, or
components with more than one cycle.

## Checks and a restriction to avoid

The explicit six- and seven-flip tables were found using the existing
Rust actual-cover model and then verified mathematically. An exhaustive
check over all 76 eligible NN instances through six vertices verifies
the theorem on all 149 connected unicyclic states containing a four-cycle
of the displayed form. These are checks of actual component membership,
not comparisons of polynomial values. The seven-vertex fixtures
area0123434 and area0123343 check another 44 and 13 such states.

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
The shared Rust sources and the Lean/manuscript sources were not changed.

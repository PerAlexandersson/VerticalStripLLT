# Inactive corrections for every unicyclic NN step

2026-09-28. We close the inactive-corner part of NN component
redistribution at arbitrary adjacent vertices a,b. This extends the
corresponding part of the
[leftmost NN proof](COMPONENT_LEFTMOST_NN_UNICYCLIC.md).
The joins between f-active components remain a separate obligation.
Primary and the existing Astra reviewer independently audited the proofs.

## Connecting redundant middle images

We retain the full saturated ordinary NN hypotheses and notation from
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md): b=a+1,
f=ac is strict, r=bc, q=ab, and σ exchanges a,b. Other strict corners
avoid a,b; every natural edge leaving either vertex ends at or before c.

Let H be a connected tree envelope omitting f,r. Consider its spanning
trees T with Env(T)=H that contain q and all the other original strict
corners, and in which a reaches c. Thus f is redundant in T+f. We compare their
middle images

    B(T)=T−q+f+r.

**Lemma.** All these middle images lie in one actual source component.

The unique increasing a-to-c path in T either skips b or starts with q.
In the first case the unique cycle of B(T) consists of f and that
path. In the second it consists of r and the b-to-c suffix. In both
cases the cycle lies inside [a,c] and uses f or r. Every incoming
edge at a or b is therefore a bridge.

First transfer each selected incoming tb to ta, using the
[incoming-bridge corollary](COMPONENT_FOUR_CYCLE_SWAP.md).
No pair ta,tb was originally selected together, since T contains q
and is a tree. These moves preserve the cycle and transfer singly
attached trees. Next transfer every selected outgoing bd to ad by the
[outgoing theorem](COMPONENT_RIGHT_ARM_TRANSFER.md). We have d<c
because T omits r. These moves need no additional incoming-edge or
cycle-location hypothesis.

The endpoint is precisely T/q on the vertex set with b identified
with a, together with f and the pendant edge r attaching b at c.
Adjacent contraction commutes with interval closure, giving

    Env(T/q)=H/q.

This envelope omits f because H omits f and r. The other original
strict corners remain maximal: they avoid a,b, and shortening an
incoming interval or extending an outgoing interval across adjacent
a,b cannot newly contain a corner avoiding these vertices.

Tree connectivity in H/q now connects the contracted trees. These
flips lift after inserting f and the pendant r. Maximality of f in
the original diagram prevents f from affecting a cover test for any
different natural edge. The pendant edge cannot affect paths between
vertices of the remaining graph. This proves the lemma, without any
assumption that the q-selected subgraph of the original tree component
is connected.

## Every inactive-f component has controlled neighbors

**Theorem.** In every eligible saturated ordinary NN diagram, each
connected unicyclic component inactive at f is either an isolated
vertex of the packet graph or has exactly one neighboring component.
In the latter case that neighbor survives the mixed-cycle reduction.

Delete the common redundant f. The
[whole-tree reduction](COMPONENT_TREE_CONNECTIVITY.md) gives a complete
tree component with envelope H, whose maximal intervals M contain a
forced increasing a-to-c path.

If this path contains b, the two cases already proved in
[the unicyclic note](COMPONENT_UNICYCLIC_REDUNDANCY.md) apply. The path
a→b→c makes the component isolated. A longer path through b gives
exactly one surviving neighbor.

Suppose instead that the path skips b. Then r is absent throughout
the component, and q is not maximal in H. The forest M∪{q} extends
to a tree of H, so there are q-selected representatives. By the
preceding lemma, all their middle images belong to one component J.
This component survives: its middle representatives have their cycle
on f, and the q-free normalization reaches a four-cycle whose only
strict cycle edge is f. Reversing f in that four-cycle is acyclic.
Every other strict edge is a bridge, so the whole mixed graph is acyclic.

It remains to check the first mixed joins from q-free states. For
a right join, introduce q by the actual flip bd→q, retaining ad.
Take the middle image, apply the full q-free σ theorem, and use
outgoing transfer to repair the held edge. This reaches J.

For a left join, the q-free source representative contains
{f,ta,tb}. The flip ta→q, retaining tb, stays in the inactive-f
component. Write this new state as

    U=S₀∪σT₀∪{f,tb,q},

where S₀ contains the other strict corners. Its middle image is

    M₀=S₀∪σT₀∪{f,tb,r}.

Since f was redundant in U, the cycle of M₀ lies in [a,c], and tb
is a bridge. The full σ theorem applies to M₀. In its image,

    σM₀=S₀∪T₀∪{f,ta,r},

ta is still a bridge, and the incoming-bridge corollary transfers it
to tb. This is exactly the required first-join endpoint. Thus every
left first join also reaches J. The initial q-introductions are actual
because f is the only redundant edge in the inactive component.

Second mixed joins select r at both endpoints and cannot meet this
inactive component. Hence J is its only neighbor, proving the theorem.

This controls every inactive-f correction in an NN packet, including
steps away from the leftmost vertex. It does not prove that two
f-active components cannot be joined directly. Components inactive at
another corner remain governed by the separate invariant in the
unicyclic note. In particular, inactive-f vertices cannot connect two
different surviving components through a path of packet joins: each
has at most one neighbor. The remaining isolation problem is therefore
concentrated in joins directly between surviving components.

## A local right q-exit

We can also handle one transition from an f-redundant state to an
f-covering state. Suppose a connected unicyclic middle representative
A selects f,q, omits r, and has f redundant. Assume there is an actual
flip q→bd retaining ad that makes f cover.

**Lemma.** A and A−q+r belong to the same actual source component.

The q-edge must lie on the increasing f-bypass, which we write as

    a→b→e→...→c.

Here e<c because r is absent. The retained ad covers while f is
redundant, so ad≠f; the NN outgoing bound therefore gives d<c.
The vertex d cannot lie on this bypass: the selected ad would then
create another cycle. Thus ad is a bridge,
d≠e, and b<d,e<c.

When d<e, use the two explicit paths in the
[leftmost NN note](COMPONENT_LEFTMOST_NN_UNICYCLIC.md), with 0,1 replaced
by a,b. Every move lies inside f, so those local paths do not require
a=0 or any condition on exterior incoming trees.

For e<d, let P be the increasing e-to-c suffix. Use

| Retained edge | Move |
| --- | --- |
| ad | q → bd |
| bd | be → ed |
| ad | bd → q |
| f | q → r |
| f,r | ad → bd, by outgoing transfer |
| bd | ed → be |
| f,r | bd → ad, by reverse outgoing transfer |

After the first move the cycle edges cover. After the second, the
cycle is {f,ad,ed} together with P, and bd is a bridge. Thus the
third and fourth moves are actual. At the endpoint of the first
outgoing transfer, the cycle is {r,bd,ed} together with P, and its
edges cover. The next flip restores be and makes only r redundant;
bd is now a bridge. The reverse outgoing theorem applies even with
r redundant and restores ad. The endpoint is exactly A−q+r.
This proves the lemma in both orders of d,e.

A q-preserving flip out of a redundant-f middle state also lifts after
q→r: deleting q preserves its required covers, and inserting r can
change only the cover status of f, by the terminal-gap geometry.
The original flip cannot use redundant f as its retained long, and
cannot exchange strict f. Thus all its cover tests survive.

The [leftward counterpart](COMPONENT_LEFT_EXIT.md) now handles a left
q-exit that exposes f, using containing corners and induction on the
incoming tail. A general tree-normalizing path can still have several
q-free states before f becomes a cover. These local transition statements
do not yet establish f-active middle-join connectivity in general.

## Verification

Exact whole-component checks pass all 76 eligible NN instances through
six vertices, with the skipped-b neighbor assertion now enforced for
every a. The seven-vertex shield fixture passes too. Direct expanded
flip paths for the new e<d case pass on five through nine vertices;
the earlier d<e paired paths are checked in the same run.

Related Rust: external `nn_component_transport.rs`, mode
`--audit-unicyclic-packet-edges`, and `right_arm_paths.rs`.
Frozen sources, commands and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/incoming-transfer/`.
These support the independently audited proofs; they do not establish
the still-open active joins. No Lean or manuscript source is changed.

# The leftmost NN step for unicyclic components

2026-09-28. We prove component isolation for the leftmost ordinary NN
recurrence in cycle rank one. Together with the packet identity, this
expresses one component as an integer combination of whole smaller
components, with the same coefficients for the coloring and HRV sums.
Primary and the independent Astra reviewer audited the argument.
The DN/DD steps and higher cycle ranks remain open for this proof route.

The later [inactive-correction theorem](COMPONENT_NN_INACTIVE_CORRECTIONS.md)
extends the inactive-f part to arbitrary eligible NN positions. Full
packet isolation proved here remains restricted to the leftmost case.

## Setting and conclusion

We retain all saturated ordinary NN hypotheses from
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md), and assume that
its adjacent vertices are a=0 and b=1. Write f=0c for the strict corner,
q=01, r=1c, and σ=(0 1). Every other strict corner avoids 0 and 1.
Every natural edge leaving either vertex ends at or before c.

We consider connected unicyclic selected states, with all selected edges
oriented forward. Components are complete components under actual flips.
A component is inactive at a strict corner if that corner is redundant
in every state. By the
[unicyclic classification](COMPONENT_UNICYCLIC_REDUNDANCY.md), a component
survives the mixed-cycle reduction exactly when it is inactive at no
strict corner. We say that it is f-active when f covers in some state;
this condition alone need not imply survival.

**Theorem.** Every leftmost NN packet contains at most one surviving
connected unicyclic source component.

We prove this by showing that middle joins from f-active components are
internal, whereas each inactive-f component is isolated or has exactly
one surviving neighbor. The other packet joins reduce to these.

## Exchanging the two leftmost vertices

The [outgoing-edge transfer](COMPONENT_RIGHT_ARM_TRANSFER.md) gives

    B ∼ B−0d+1d,       1<d<c,

whenever B contains f,r,0d and omits q,1d. It applies whether 0d is a
bridge or lies on the unique cycle, and fixes all other selected edges.
Its reverse applies when only 1d is selected: replacing 1d by 0d
preserves connectedness because f,r already connect 0 and 1, and edge
count then preserves the unicyclic condition.

Consequently every connected unicyclic B selecting f,r and omitting q
satisfies B∼σB. Indeed, there are no incoming edges at 0 or 1.
Transfer each singly selected pair 0d,1d in turn. Pairs with both or
neither edge selected require no change. All other edges are fixed.
No assumption about the location of the unique cycle is needed here.

## Connecting all middle images of one tree envelope

Let H be a connected tree envelope omitting f,r. Let T range over
its spanning trees with envelope H that select q and retain all other
original strict corners. We claim that the states

    B(T)=T−q+f+r

belong to one complete source component. They are connected unicycles:
we replace the tree edge q by the two-edge path 0–c–1.

No T can select both 0d and 1d, since it already selects q. In B(T),
transfer every selected 1d, d<c, to 0d, using the preceding theorem.
The result is T/q, with vertex 1 identified with 0, together with f
and the pendant edge r attaching vertex 1 at c.

Adjacent contraction commutes with interval closure, so
Env(T/q)=H/q independently of T. This envelope omits f, since H omits
both f and r. The other original strict corners remain maximal:
they avoid 0,1, and a new interval 0d obtained from 1d lies properly
inside f, hence cannot contain another strict corner.

The tree-connectivity theorem in
[the tree note](COMPONENT_TREE_CONNECTIVITY.md) connects the trees T/q.
These flips lift after adjoining f and the pendant edge r. Inserting
the maximal interval f cannot change a cover test for a different
natural edge; the pendant edge cannot affect a path between vertices
of the remaining graph. Thus all B(T) belong to one component.
This conclusion does not require the q-selected subgraph of the
original tree component to be connected.

## Forced reachability with a prescribed forest

We need a slight extension of the forced-tree-path lemma. Let M be
the maximal intervals of a connected interval-closed graph H, and
let F be any forest with M⊆F⊆H.

**Lemma.** A directed u-to-v path occurs in every spanning tree of H
containing F if and only if it already occurs in F.

A path in F is retained in every extension. Conversely, if u,v lie
in the same component of F, their unique path in every tree extension
is the path in F, proving the assertion in this case.

Suppose they lie in different components. The directed quotient H/M
is strongly connected, by the return-walk argument in the tree note.
The quotient H/F is a further contraction and is therefore strongly
connected too. Choose a simple directed quotient path from [v] to [u],
lift its edges, and adjoin F. This is still a forest, since the added
edges join distinct F-components along a simple path. Extend it to a
spanning tree of H. Its unique u–v path traverses the added edges
backwards, and so is not directed from u to v. This proves the lemma.

## Middle joins from f-active components

A middle join has representatives A and B=A−q+r, where A selects
f,q and omits r. Suppose that the component C containing A is
f-active. We prove B∈C.

If f covers in A, the flip q→r retaining f proves this directly.
Otherwise T=A−f is a tree. Put H=Env(T), with maximal intervals M.
All trees with envelope H become states in C after insertion of f:
tree connectivity lifts because f is maximal. If M forced 0→c,
the whole-component insertion theorem would make C inactive at f.
Thus M has no such directed path.

Put F=M∪{q}. This is a forest: the maximal intervals form increasing
chains, and adjacent vertices 0,1 can be in the same chain only when
q already belongs to M.

If F does not force 0→c, the preceding lemma supplies a tree T′
extending F in which f covers after insertion. Its middle join is
an actual flip. All middle images of the envelope H are connected
by the preceding section, so the original B also belongs to C.

It remains to handle the case where F forces 0→c but M does not.
Then q∉M. The connected envelope H has a maximal edge 0d, with d>1,
and M contains an increasing chain

    1→e=x₀→x₁→...→xₖ=c.

Maximality gives d<e: otherwise 1e would be contained in 0d.
Moreover e<c because r∉H. Thus 1<d<e<c.
Choose a tree T* extending F. Its displayed edges are q,0d,1e and
the path P from e to c. Every other edge belongs to a tree attached
at one vertex of this displayed tree. Such attachments do not change
any of the cover tests below and remain fixed throughout.

We give paths from both A*=T*+f and B*=T*−q+f+r to the same state.
Starting from A*, use the following moves in order:

| Retained edge | Exchanged edge |
| --- | --- |
| 0d | q → 1d |
| f | 0d → dc |
| 1e | 1d → de |
| 0xᵢ₊₁ | xᵢxᵢ₊₁ → 0xᵢ, for i=k−1,...,0 |
| 0e | 1e → q |
| f | q → r |

The sweep begins with retained edge 0c=f. Initially only f is
redundant. The first move breaks its bypass. After the third move,
dc is the only redundant edge, through de and P; the first sweep
move breaks that bypass. The remaining cycle edges cover throughout
the sweep. At its end 1e is pendant, so the last two moves are actual.

Starting from B*, use

| Retained edge | Exchanged edge |
| --- | --- |
| 0xᵢ₊₁ | xᵢxᵢ₊₁ → 0xᵢ, for i=k−1,...,0 |
| f | 0d → dc |
| r | 1e → ec |
| dc | ec → de |

Initially only r is redundant. The first sweep move breaks its
bypass, while f is a bridge. The sweep ends with the four-cycle
{f,r,0e,1e} and pendant edge 0d. The next two moves are actual;
the second makes only f redundant. The final move uses ec and dc,
which still cover. Both paths end at

    {f,r,de,dc,0x₀,...,0xₖ₋₁}

together with exactly the same exterior edges. Every exchanged edge
lies properly inside f and is normal. Thus A* and B* lie in the
same actual component. Tree connectivity gives A*∈C, and middle-image
connectivity connects B* to B. This proves B∈C in the final case.

## The inactive-f components

Let I be inactive at f. Deleting f identifies I with a whole tree
component of envelope H, whose maximal intervals force a path 0→c.
If that forced path passes through 1, the earlier
[inactive-f classification](COMPONENT_UNICYCLIC_REDUNDANCY.md) applies:
the path 0→1→c makes I isolated, and a longer path through 1 gives
exactly one neighboring component, which survives.

Suppose the forced path skips 1. Then r is absent throughout I and
q is not maximal in H. The forest M∪{q} extends to a tree of H,
so q-selected representatives exist. The middle images of all such
representatives lie in one component J by the middle-image theorem.

This component survives. Its middle representatives retain the forced
f-bypass skipping 1, so f lies on their unique cycle. The q-free
normalization in the [four-cycle note](COMPONENT_FOUR_CYCLE_SWAP.md)
reaches a four-cycle with f as its only strict cycle edge. Its mixed
graph is acyclic, proving that J survives.

Every first mixed join from a q-free state of I contains f,0d,1d.
The actual flip 1d→q retaining 0d gives a q-selected state of I.
Its middle image differs from the first-join neighbor by σ and one
held-edge transfer. Both are actual-component connections by the
first section and the outgoing-edge theorem. Hence that neighbor is
also J. There are no left overlaps at 0, and a second mixed join
selects r at both endpoints, so cannot meet I. We have proved that
I has exactly one neighboring component, namely J.

## Packet isolation and the component recurrence

Every second mixed NN join is internal by the four-cycle theorem.
Every first mixed join reduces to a middle join: introduce q by the
actual flip retaining 0d, pass across the middle join, and use σ and
the outgoing-edge transfer to reach the required endpoint. The needed
short edges cover because the join comes from an actual target flip.
Its q-free target endpoint is the adjacent-swap image of the first
source representative. Since 0,1 are adjacent and q is absent, this
swap preserves directed paths and covers. The two short edges must
cover in the target flip, and hence also in the source.
There are no left first joins at a=0.

The middle joins from f-active components are internal. Each remaining
component is inactive at f and, by the preceding section, is isolated
or has exactly one surviving neighbor. Thus a packet cannot connect
two distinct surviving components. This proves the theorem.

For completeness, the invariant proved in the unicyclic classification
also shows that a packet meeting a surviving component contains no
component inactive at a different strict corner. Consequently a packet
containing a surviving C is of the form C together with inactive-f
components I₁,...,Iₘ. Apply the NN packet identity to its indicator.
The target multiplicity is the indicator of a union U of complete
target components. Delete f in each Iⱼ to obtain a whole tree
component Tⱼ. We obtain, simultaneously for X=K and X=E,

    X(C) = Σ_{D∈U} X(D) − Σⱼ X(Tⱼ).

Both target diagrams and the corner-deleted correction diagrams are
smaller in area. If C itself is inactive, its direct whole-tree
reduction already supplies the required identity. This closes the
leftmost NN induction step for connected unicyclic source components.
It does not establish that every component admits such a step, nor
settle DN/DD or larger cycle ranks.

## Verification and provenance

Primary and the existing Astra reviewer independently checked the
forest lemma, both displayed paths, middle-image connectivity, the
inactive cases, and the final isolation deduction. Exact Rust checks
pass all 41 eligible leftmost NN instances through six vertices and
the seven-vertex fixtures area0123434 and area0123234. The latter have
no distinct packet joins; they check the structural assertions only.
The paired paths also pass individual cover tests on five through
nine vertices. These finite checks support the proofs, not replace them.

Related Rust: external `nn_component_transport.rs`, with
`--scan-unicyclic-packets --audit-unicyclic-packet-edges --leftmost-only`,
and `right_arm_paths.rs`. Frozen consumers, model, manifests, receipts
and commands are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/leaf-envelope/`.
No Lean declaration or manuscript replacement is claimed.

# Completing the tree pieces of a unicyclic NN image

2026-09-28. For one connected unicyclic source component, we give a uniform
repair of its NN image. The repair completes every tree piece where r is
absent, preserves every q-preserving flip equality, and leaves the already
complete selected-r tree pieces unchanged. We also complete every target
unicyclic component inactive at r.

The [left comparison](COMPONENT_NN_LEFT_REASSEMBLY.md) completes the remaining
sector for components active at every strict corner. Combined with deletion
at any inactive corner, it proves the complete connected unicyclic NN
reduction. This note supplies the simultaneous correction used there.

## Setup and the components used in the repair

We retain the saturated ordinary NN setting: f=ac is the strict corner,
b=a+1, q=ab, r=bc, σ swaps a,b, and D0=L−f. Write w_C for the canonical
coefficient vector of one source component C from the
[direct NN split](COMPONENT_NN_REDISTRIBUTION.md). Thus

    X(C)=Σ_T w_C(T)X(T),                   X=K,E,

with

    w00=0,              w10=h10−h01,
    w01=(h00+h01)∘σ,     w11=h11+h01.                  (1)

Here h is the indicator of C. We use the same coefficients for the strict
coloring sum K and the HRV elementary expression E.

A component is inactive at f if f is redundant in every state. Deleting
f from such a connected unicyclic component I gives an entire tree
component D_I of D0, and

    X(I)=X(D_I),                         X=K,E.        (2)

This is the [whole-tree deletion lemma](COMPONENT_TREE_CONNECTIVITY.md),
which uses equality of reachability and of the complete flip graphs.
It does not assume the component HRV formula. Thus an inactive source
component is already reduced to a smaller diagram.

Now suppose C is active at f. Let J(C) consist of the inactive components
I whose middle images belong to C. More precisely, a middle image replaces
q by r in a state selecting f,q and omitting r. The proved
[inactive-corner theorem](COMPONENT_NN_INACTIVE_CORRECTIONS.md) says that
every nonisolated inactive I has exactly one such neighboring component.
That neighbor is active at f. All states of a nonisolated I omit r.
The [active-middle theorem](COMPONENT_NN_MIDDLE_JOINS.md) says that a
middle image of a state in an f-active component remains in that component.

The simultaneous repair below uses only these middle identifications.
We do not require C to be isolated in the larger graph of all imposed
NN joins. The later inactive-r argument also uses the unique-neighbor
theorem for first mixed joins.

## One simultaneous repair

Define

    w̃_C = w_C + Σ_{I∈J(C)} (w_I − 1_{D_I}).             (3)

Every summand has zero K and E valuation, by (1) and (2). Hence w̃_C still
represents X(C) for both valuations.

Set h=1_C+Σ_{I∈J(C)}1_I. Then h10=h01 for every exterior selection Q.
Indeed, the two middle states have the same weak-component partition and
edge count. If they are not connected unicycles, both indicators vanish.
Otherwise, if the 10 state belongs to an f-active component, the middle
theorem identifies its component with that of the 01 state. If it belongs
to an inactive I, either the two components agree or the 01 state is in
the unique active neighbor of I. In the latter case both belong to h
exactly when that neighbor is C. These are all possibilities.

By linearity, the sum w_C+Σ_I w_I is the canonical vector of h. Its
r-absent sector is therefore zero, since w00=0 and w10=h10−h01=0.
Subtracting the whole D_I in (3) gives the exact pointwise formula

    w̃_C(T)=−Σ_{I∈J(C)}1_{D_I}(T)       when r∉T.       (4)

Thus the entire r-absent sector is a sum of complete smaller components.
In particular, we have completed the negative tree pieces, including
their q-absent states.

Every canonical w_I is constant across q-preserving target flips by
the [NN overlap lemma](COMPONENT_NN_OVERLAPS.md). Every 1_{D_I} is constant
across all target flips. Consequently the simultaneous repair preserves
all q-preserving equalities throughout D0. This is the compatibility that
cannot be inferred from a repair at just one boundary.

## What the repair moves

There is a more explicit description of each summand in (3). For a
nonisolated inactive I, all its states omit r. A tree T∈D_I containing
q contributes itself to w_I. A tree T∈D_I omitting q contributes the
target state σ(T+f), which selects r. Therefore

    w_I−1_{D_I}
      =Σ_{T∈D_I, q∉T} (1_{σ(T+f)}−1_T).               (5)

Each displayed difference has zero valuation separately. The edge f is
redundant in T+f, so X(T+f)=X(T). The NN bottom relabeling gives
X(σ(T+f))=X(T+f), for both K and E. The new target state is connected
and unicyclic; it has one more selected edge than T.

Thus the repair subtracts the missing q-absent part of a complete deletion
tree component and places it on the selected-r side. Formula (3), rather
than any assumption about separate terms of (5), proves that all
q-preserving equalities survive.

For the earlier four-vertex example, use edge names

    A=01, B=02, C=12, D=13, E=23, F=03.

The inactive component I={FABE,FBCE} has deletion component
D_I={ABE,BCE}. Only BCE omits q=A. Formula (5) is exactly

    [BCDE]−[BCE]=0,

the single repair in the [sixteen-case table](COMPONENT_FOUR_EDGE_CASES.md).
The general construction therefore recovers that explicit completion of
two incomplete target pieces at once.

## The remaining target sector

The corrections in (5) affect only r-absent trees and connected selected-r
unicycles. In particular, they leave every connected selected-r tree
coefficient unchanged. Those coefficients are already constant on whole
components by the [tree-sector theorem](COMPONENT_NN_TREE_SECTORS.md).

We also account for disconnected outputs. A connected unicyclic source
has n selected edges. By (1), target states have n or n−1 edges.
The n-edge selected-r terms come from relabeling a connected source state
or replacing f by q while retaining r; both operations preserve weak
connectedness. They are connected unicycles.

At n−1 edges, the h11 term deletes redundant f from a state containing
f,q,r, and therefore produces a connected tree. The other possibility
comes from h01 in w01: remove r from a connected source state containing
f,r, then apply σ. If this disconnects the state, f keeps a,c together
before the swap and b lies in the other block. After the swap, a is in
a different weak block from b,c. Hence q is absent throughout the entire
target component. Every flip there preserves q, so its coefficients are
already constant. These disconnected outputs consist of two weak blocks
with one cycle in total; the repair (5) does not alter them.

Together with (4), this leaves only q-changing flips between connected
selected-r target unicycles. We can settle one more whole family.

## Target components inactive at r

Let D be a complete connected target unicyclic component in which r is
always redundant. Deleting r gives a whole tree component with envelope H,
whose maximal intervals M contain a forced increasing chain

    b=d0<d1<…<dk=c.

Take T∈D with q absent, and put B=T−r. The NN bottom source state is
U=σT=f+σB. We claim that it belongs to a component inactive at f.

The chain a<d1<…<dk=c consists of maximal intervals in Env(σB). For its
first edge ad1, any selected edge xy of σB containing it has x≤a and
y≥d1>b. Applying σ inversely gives an edge of B containing bd1; proper
containment remains proper. This contradicts maximality of bd1 unless
the two edges agree. For every later chain edge di di+1, we have di>b.
An edge containing it still contains it after the inverse swap, since
swapping a,b cannot cross di. The original chain edges are maximal, so
the later transformed edges remain maximal as well.

The forced-tree-path theorem therefore places U in an entire f-inactive
component I. This is stronger than merely observing that f is redundant
in this particular state.

Suppose T↔T′ is an actual target flip changing q from absent to selected.
On this n-edge layer, the two repaired coefficients are

    w̃_C(T)=h(σT),           w̃_C(T′)=h(T′−q+f),

since the other terms of (1) would have n+1 source edges and the subtracted
D_I are trees. These source states U,V are exactly the first mixed NN
join associated with this target flip.

The unique cycle of T′ consists of r and an increasing b-to-c bypass.
It lies in [b,c], so q=ab is a bridge. After q is removed, r keeps b,c
together; inserting f rejoins the same cut. Thus f is a bridge in V,
and V belongs to an f-active component. The inactive-corner theorem
identifies that component as the unique neighbor of I. By the definition
of h, either both source states are included or both are excluded.
Consequently the repaired coefficients agree across this flip.

They already agree across every q-preserving flip. Hence w̃_C is constant
on the whole component D. This completes the target components inactive
at r without a new valuation identity or a packet-isolation hypothesis.

The only obligation left by these reductions is the first mixed comparison
inside connected selected-r target unicyclic components active at r.

The subsequent [active-component swap](COMPONENT_NN_ACTIVE_SWAP.md) settles
every right first comparison after reducing source components inactive at
a strict corner. The [left comparison](COMPONENT_NN_LEFT_REASSEMBLY.md) now completes cycle rank one.

## Verification and provenance

Primary and the existing independent Astra reviewer derived and checked
the simultaneous repair, its statewise form, and the disconnected sector.
No full component-expansion theorem is used.

Related Rust: external `nn_component_transport.rs`,
`--audit-inactive-reassembly`, reuses the established actual-cover component
enumeration and shared graph API. It checks complete deletion components,
all middle coefficients, the full repaired vector, all q-preserving flips,
the support of every remaining discrepancy, and the pointwise relocation
in (5). Frozen sources and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-inactive-reassembly/`.

All 76 eligible NN instances through six vertices pass: 31 f-active
source components, 46 correcting inactive components, 8,396 middle
comparisons, 33,584 repaired state coefficients, and 28 inactive-r target
component comparisons. The seven-vertex area (0,1,2,3,4,3,4), at corner 26,
adds two f-active sources, one inactive correction, 16,384 middle checks,
65,536 state coefficients, and two inactive-r target comparisons.
No coefficient discrepancy remains in these finite instances. In addition,
all 163+65 individual relocations in (5) pass independent exact K and E
valuation checks. This finite absence of discrepancies is not the missing
uniform proof for target components active at r. All final runs exit zero.

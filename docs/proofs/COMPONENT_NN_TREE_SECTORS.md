# Complete tree components in the NN recurrence

2026-09-28. We push the connected source tree component through the NN
recurrence and collect its entire image into complete smaller components.
We also identify the coefficient of every selected-r target tree component
for an arbitrary source component. Both statements are proved below;
they do not settle redistribution for all source components.

## Setting

We use an eligible ordinary NN step in a saturated source diagram L.
Its strict corner is f=ac, with b=a+1, q=ab and r=bc. Let D0=L−f;
r is a normal natural corner in D0. Write σ for the adjacent swap a,b.
Other strict corners are fixed by σ. All states retain the prescribed
strict edges. We assume L has a connected spanning tree state.

All connected source trees have the full source interval envelope, since
they contain every maximal natural edge. By
[tree connectivity](COMPONENT_TREE_CONNECTIVITY.md), they form one
complete source component C_tree. We use only this connectivity theorem,
not the HRV formula for tree components.

For a fixed source component C, let h_ij(Q) indicate that the state
L_ij(Q)=Q+f+iq+jr belongs to C. The
[direct NN split](COMPONENT_NN_REDISTRIBUTION.md) gives

    X(C)=Σ_T w_C(T)X(T),                 X=K,E,

with the same target coefficients for both valuations:

    w00=0,              w10=h10−h01,
    w01=(h00+h01)∘σ,     w11=h11+h01.                 (1)

We identify these coefficients before applying any further diamonds.

## The recurrence for the connected source tree component

Let F be the following union of states in D0:

* connected spanning trees selecting r;
* spanning forests with two weak components, selecting r, in which a
  and c belong to different components.

Then

    X(C_tree)=Σ_{D ⊆ F} X(D),             X=K,E,       (2)

where the sum is over complete D0 flip components. Every coefficient is
one. Since r is a natural corner, its selected status is flip-invariant.
Flips also preserve the number of selected edges and the weak-component
partition. Consequently both displayed families are unions of complete
components, as required for (2).

**Proof.** Set C=C_tree in (1). A source state has nonzero indicator
exactly when it is a connected tree. Hence only target states with n−1
or n−2 selected edges can contribute, where n is the number of vertices.

First take a target state T with n−1 edges. In sector 01 the only
possible term is h00(σQ), whose source state is σT. It is a connected
tree exactly when T is. In sector 11 the only possible term is h01(Q),
whose source state is T−q+f. Since T contains q and r, replacing q by
f preserves connectedness in both directions: after deleting q from a
tree, r keeps b,c on the same side of the cut, and f rejoins the cut.
Conversely, in a tree containing f,r, deleting f separates a from b,c,
and q rejoins it. Thus this source state is a tree exactly when T is.
The other two sectors have coefficient zero at this edge count.

Now take T with n−2 edges. In sector 10, the two source states are

    S10=T+f,             S01=T−q+f+r.

Either both are connected trees or neither is. Indeed, in a tree
containing f,q, removing q separates b from a,c and inserting r rejoins
the cut. The reverse exchange works in a tree containing f,r. Every
connected source tree belongs to C_tree, so h10−h01=0.

In sector 01, only h01(σQ) can contribute. Its source state is
σ(T+f), so its indicator is one exactly when T+f is a connected tree.
Equivalently, T is a two-component forest separating a,c. In sector 11,
only h11(Q) can contribute, but its source state T+f contains the
triangle f,q,r and is not a tree. Sector 00 again has coefficient zero.

These arguments apply to all target states of the indicated sizes;
we have not assumed in advance that T is a forest. They give precisely
the indicator of F. Grouping its states by complete components proves
(2). The same coefficient computation applies to K and E. ∎

## Selected-r target trees for any source component

Let D be a complete connected tree component of D0 selecting r.
Adding the maximal edge f lifts every flip of D: a directed path using
f cannot bypass another natural edge, since that edge would contain f.
Thus all states T+f, for T∈D, lie in one source component C_D.
They are connected unicyclic states, with f on the unique cycle.

For every source component C and every T∈D, we have

    w_C(T)=1_{C=C_tree}+1_{C=C_D}.                       (3)

In particular, D already occurs with a constant coefficient in the
initial image of C. It requires no repair. The two source components
in (3) are distinct, since their selected-edge counts differ.

**Proof.** If q is selected, (1) gives h11(Q)+h01(Q). The first source
state is T+f, in C_D. The second is T−q+f, a connected source tree by
the cut argument above, hence in C_tree.

If q is absent, (1) gives h00(σQ)+h01(σQ). The first source state is
σT, again in C_tree. The second is σ(T+f). The state T+f selects f,r,
omits q, and its unique cycle contains f. The proved
[unicyclic adjacent-swap theorem](COMPONENT_FOUR_CYCLE_SWAP.md) therefore
connects T+f to σ(T+f) by actual source flips. Hence the second indicator
is precisely 1_{C=C_D}. This proves (3). ∎

This assertion concerns target trees selecting r. Target trees omitting
r, as well as targets with cycles, still require their own bookkeeping.

## Checks and provenance

Primary and the existing independent Astra reviewer derived and audited
both coefficient formulas and the complete-component collection. No
claim here uses the previously formalized component-expansion theorem.

Related Rust: the external `nn_component_transport.rs` consumer,
`--audit-tree-sector`, reuses the actual cover-flip enumeration and
`combinatoric_core::graph::Graph::is_connected`. It checks (3) for every
source component and checks the entire coefficient vector in (2), including
zero coefficients on nonforests. Receipts and frozen sources are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-all-components/`.
The checks support the proofs; they are not the proof of the general case.

The exhaustive scan of all 76 eligible NN instances through six vertices
checks 3,647 source components: 555,547 selected-r tree coefficients and
30,528 entries of the full coefficient vectors for the 29 connected source
tree components. Those vectors collect into 131 complete output components.
The separate six-vertex fixture has five output components for C_tree.
All assertions pass; the Cargo processes finished with exit zero.

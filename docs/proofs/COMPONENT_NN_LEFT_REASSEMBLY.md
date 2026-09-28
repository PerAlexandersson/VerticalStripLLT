# The left comparison and the unicyclic NN recurrence

2026-09-28. We complete the NN reassembly for a connected component with
one cycle. The remaining comparison moves an incoming edge from a to b.
The actual target flip supplies the cover hypotheses needed for this
move. We first handle an edge on the cycle by induction on its tail,
then expose a redundant containing corner when the edge is a bridge.

We use the saturated ordinary NN setting, with b=a+1, strict corner
f=ac, q=ab, r=bc and σ=(a b). Other strict corners avoid a,b, and
outgoing edges at a,b have heads at most c. Every incoming edge ta,
t<a, has a selected strict container g=uv satisfying

    u≤t<a<b<v<c.                                      (1)

We write W∼W′ for membership in the same actual flip component.
All tree normalizations below use the
[tree-connectivity theorem](COMPONENT_TREE_CONNECTIVITY.md), retaining
the maximal intervals of the tree envelope and hence all strict edges.

For a bridge transfer we use the earlier
[strict-cover theorem](COMPONENT_NN_FIRST_JOINS.md#a-containing-corner-in-a-different-attached-tree)
when the cycle avoids f,r, and the
[cycle-containing-corner corollary](COMPONENT_FOUR_CYCLE_SWAP.md#transferring-a-single-incoming-bridge)
otherwise. These results precede the on-cycle argument below.

## Transferring an edge on the cycle

**Theorem.** Let W be connected and unicyclic, select f,r,ta, and omit
q,tb. Suppose ta lies on the unique cycle. Put W′=W−ta+tb. If ta
covers in W and tb covers in W′, then W∼W′.

We do not assume that a containing corner has the same tail t.
We prove the theorem by strong induction on t. The common tree Y=W−ta
contains the path a–c–b. Let k be the vertex where the path from t first
meets this path; thus k is a,b or c. The unique cycle of W consists of
ta and the t–a path in Y; that of W′ uses tb and the t–b path.

### When tv is already selected

We first extend the [selected-interval transfer](COMPONENT_INCOMING_EDGE_TRANSFER.md)
to every position of the cycle. Suppose tv is selected for b<v<c.
If k=b or c, the cycle of W uses f or r and that theorem applies.
If k=a, the cycle of W′ uses f,r. Apply the theorem to σW′, whose
transfer endpoint is σW. The established
[cycle-position swaps](COMPONENT_NN_ACTIVE_SWAP.md#a-state-where-all-strict-edges-cover)
give W∼σW and W′∼σW′: each cycle meets a or b, and these particular
swap results require no activity hypothesis. This proves the transfer
whenever tv is selected.

### When the common path meets at c

Suppose k=c. Deleting f,r from Y leaves three trees, rooted at a,b,c;
the last contains t. Denote it by K. Choose a strict container g=uv
as in (1).

First arrange that g lies in K. If it lies in the a-tree, normalize the
path from a to v inside [a,v]. Its first edge is ax, where b<x≤v<c,
since b is not in this tree. Exchange ax with xc, retaining f, in
both endpoints. The edge ax is a bridge. The edge f covers in W
because the other cycle edge at a is incoming ta; it is a bridge in W′.
The move transfers the whole attached tree containing g into K. If g
lies in the b-tree, do the same with bx→xc, retaining r. These common
preparations preserve the cycles and restore all original edges when
reversed.

Let M be the maximal intervals of K's envelope. If t=u, tv=g is already
selected. Otherwise u<t<v, and t,v lie in different M-chains: a chain
joining them would contain the edge uv and start below t. Hence M+tv
is a forest, and extends to a spanning tree with the same envelope.
Normalize K to that tree in both endpoints.

These two local tree paths lift despite the exterior directed path
from t to c, through a in W and through b in W′. Indeed, tc is not
natural: it would properly contain the strict corner f. No local
natural edge can therefore contain the interval [t,c]. An exterior
t-to-c path cannot destroy a local cover, since such a destroyed cover
would have to contain this interval. All other exterior trees meet K
at one vertex. At the normalized endpoints tv is selected, so apply
the preceding transfer and reverse the preparations. This proves the
case k=c.

### Reducing to a sink at a

For k=b, apply σ to both endpoints and reverse their roles. The new
initial state is σW′, its exchanged edge is ta, and its branch point
is a. Both endpoint covers are preserved by this q-free relabeling.
The unconditional cycle-position swaps connect the original and swapped
endpoints. It therefore suffices to treat k=a.

If the other cycle edge at a is outgoing ad, then b<d<c. Use the
same flip ad→dc, retaining f, in W and W′. Both required edges cover:
f is a bridge in W, while an alternate a-to-c path in W′ would have
to pass through t<a. A bypass of ad would give a cycle entirely in
[a,d], whereas the unique cycle contains t. The new branch point is
c, so the preceding case applies. Undoing the paired flip finishes.

We are left with a sink at a: the two cycle edges there are ta,sa,
with s<a. Remove a and every tree attached there from W. The remaining
graph R is a tree containing t,s. The fixed exteriors at our two
endpoints connect these ports by

    t → a ← s,             t → b → c ← a ← s.

Neither gives a directed path between t and s. Thus any common
same-envelope normalization of R lifts to both endpoints by the
[tree-lifting lemma](COMPONENT_NN_FIRST_JOINS.md).

If g lies in R, extend its maximal forest by tv, as in the preceding
case, and normalize R to select tv. The selected-interval transfer,
followed by the reversed normalization, proves the claim.

### A containing corner in an attached tree

It remains that g lies in a tree attached at a, possibly through c,b.
In particular, g is a bridge and covers. We first put it in a branch
at a containing neither b nor c.

If it lies in the b-tree, normalize the b–u path inside [u,b]. Its
first edge xb has u≤x<a. Move this bridge from b to a, separately at
both endpoints, using the
[incoming-bridge theorem](COMPONENT_NN_FIRST_JOINS.md#a-containing-corner-in-a-different-attached-tree)
with the strict covering container g. If it lies in the c-tree,
normalize the c–v path and exchange its first edge xc with ax,
retaining f. Here b<v≤x<c; f covers in both endpoints, being either
a bridge or a cycle edge whose other incident cycle edge at a is
incoming. All normalizations take place in a singly attached tree.

Now normalize this common g-branch from a towards u, with first edge
xa, u≤x<a. The vertex x is outside the original cycle, so x≠t.
At W′ only, use the incoming-bridge theorem to move this branch from
a to b. We now compare a state selecting ta,xa with one selecting
tb,xb; every other edge agrees.

If t<x, make the paired flips

    xa → tx, retaining ta;       xb → tx, retaining tb.

The retained edges cover by hypothesis, and the exchanged edges are
bridges. The g-branch is now attached at t, inside the common tree R.
The preceding argument applies, and reversing the preparations gives
the original comparison.

If x<t, use instead

    ta → xt, retaining xa;       tb → xt, retaining xb.

The resulting states differ by xa versus xb. These edges lie on their
respective cycles and cover. To check the last assertion, a bypass of
xa would have to start with the new edge xt and continue along an old
t-to-a bypass of ta. This contradicts the original cover hypothesis.
The same argument applies to xb and tb. The original g-branch has no
other connection to the rest of the graph, so it supplies no additional
bypass. All strict corners remain selected, f,r remain selected and
q remains absent. We may apply the induction hypothesis to x<t, then
reverse the two preparations. This completes the on-cycle proof.

## Exposing a containing corner for a bridge

**Theorem.** Let W select f,r,ta and omit q,tb, with ta a bridge.
Suppose W is connected and unicyclic and its component is active at
every strict corner. Then W∼W−ta+tb.

Choose a selected strict container g=uv as in (1). If g covers, the
existing incoming-bridge theorem proves the claim. Suppose g is
redundant. Put

    W′=W−ta+tb,       Y=W−g,       Y′=Y−ta+tb.

Both Y,Y′ are trees. Their envelopes satisfy H=Env(Y)⊆Env(Y′)=H′,
since tb contains ta. Let M be the maximal intervals of H and set

    F=M+f+r+ta,             F′=F−ta+tb.

These are forests with the same weak-component partition: f,r already
connect a,b. Moreover F′ contains every maximal interval of H′.
Enlarging ta to tb can only add the maximal interval tb and remove
old maxima which it contains.

The increasing bypass of g in Y avoids ta, since ta was a bridge
in W, and avoids f,r, whose head c is larger than v. If F connected
u,v, its unique path would be this bypass and would already lie in M.
But M cannot force u→v: the
[whole-tree insertion theorem](COMPONENT_TREE_CONNECTIVITY.md)
would then make the component of W inactive at g. Thus u,v belong
to different components of F, and also of F′.

The [prescribed-forest lemma](COMPONENT_LEFTMOST_NN_UNICYCLIC.md#forced-reachability-with-a-prescribed-forest)
gives a directed path from [v] to [u] in H/F. Lift a simple such path
and extend F to a spanning tree Y*. Use exactly the same added edges
with F′ to obtain Y*′. This is a tree because F and F′ have the same
component partition. Its envelope is H′: it contains all maxima of
H′, and every new edge belongs to H⊆H′. We have

    Env(Y*)=H,                 Env(Y*′)=H′.

The unique u–v paths in both trees traverse the chosen quotient edges
backwards. Consequently g covers in both W*=Y*+g and W*′=Y*′+g.
Every selected edge then covers: a different redundant edge would have
to contain the strict corner g on its unique cycle.

Separate tree paths connect Y to Y* and Y′ to Y*′. Reinserting maximal
g lifts both paths, since no natural edge can properly contain g.
At the exposed endpoints, use the old incoming-bridge theorem if ta
is a bridge and the on-cycle theorem above otherwise. We obtain

    W ∼ W* ∼ W*′ ∼ W′.

The construction need not preserve the bridge status of ta; the
on-cycle theorem is precisely what allows the final alternative.

## The left first comparison

Consider an actual left target flip, with connected unicyclic states

    T₀=Q+ta+tb+r,            T₁=Q+tb+q+r.

Its first source comparison is

    U=σQ+ta+tb+f,            V=Q+tb+f+r.

Suppose U belongs to a component active at every strict corner. The
target cover tests, transported by σ, permit ta→q retaining tb in U.
The [active-middle theorem](COMPONENT_NN_MIDDLE_JOINS.md) then replaces
q by r within the same component. The full
[active-component swap](COMPONENT_NN_ACTIVE_SWAP.md) gives

    B=Q+ta+f+r.

The edge ta covers in B, and tb covers in V. Indeed, T₀ tested both
edges as covers; deleting the opposite short cannot introduce a bypass,
and the new edge f ends at c>b, so it cannot enter a path ending at
a or b. If ta lies on the cycle of B, apply the on-cycle theorem.
If it is a bridge, apply the active-component bridge theorem. Thus
U∼B∼V, proving the left comparison.

## Collecting complete smaller components

Let C be a connected unicyclic source component active at every strict
corner. For each adjacent f-inactive component I, let D_I be its whole
deletion-tree component, and let J(C) be the set of these I. Use the
[simultaneous repair](COMPONENT_NN_UNICYCLIC_REASSEMBLY.md)

    w̃_C=w_C+Σ_{I∈J(C)}(w_I−1_{D_I}),
    h=1_C+Σ_{I∈J(C)}1_I.

Every added difference has zero coloring and HRV valuation. Across a
left q-changing flip in the connected selected-r unicyclic target
sector, the two coefficients are h(U) and h(V). If U is in a component
active at all strict corners, the preceding theorem identifies its
component with V's. If it is inactive at f, the unique-neighbor theorem
gives equal h-values. If it is inactive at another strict corner, that
inactive corner is preserved by the first comparison, and both values
are zero. Hence the repaired coefficients agree across every left flip.

The right comparisons are already proved in the active-swap note.
Together with q-preserving constancy, the completed tree sectors and
the disconnected sectors, this proves that w̃_C is constant on every
complete component D of the smaller diagram D0=L−f. Writing this
constant as m_D, we obtain the component recurrence

    X_L(C)=Σ_D m_D X_D0(D),                 X=K,E.      (2)

The same integers m_D occur on both sides. They are obtained by the
explicit NN split and the stated zero-valuation repairs. If a connected
unicyclic source component is inactive at a strict corner g, we instead
delete g and obtain a whole tree component with the same two valuations.
Thus every connected unicyclic component admits the required reduction
at an eligible saturated NN step.

This proves the NN step in cycle rank one. General DN/DD reassembly,
recurrence coverage and higher cycle ranks remain open.

## Internal verification

Primary and the existing independent Astra reviewer checked the on-cycle
induction, the paired exposure and the final left coefficient comparison.
The proof does not use the completed word/component HRV theorem.
Related Rust: external `nn_component_transport.rs` and
`first_join_tree_lifts.rs`, reusing the established exact actual-flip model.
Receipts, frozen sources and detailed check counts are recorded under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-left-transfer/`.

The complete-vector scan covers all 76 eligible NN instances through six
vertices, including 93 left and 511 right comparisons. The seven-vertex
area (0,1,2,3,4,3,4), at corner 26, adds 217 left and 216 right comparisons.
All assertions pass. A six-vertex fixture checks the two separate exposure
tree paths and the resulting on-cycle transfer. An eight-vertex fixture
checks the smaller-tail step from 2 to 0, including both new cover tests
and explicit actual paths for the preparatory and terminal transfers.
These finite checks accompany the general proofs above.

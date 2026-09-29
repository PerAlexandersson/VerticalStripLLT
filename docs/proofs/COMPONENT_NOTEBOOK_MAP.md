# The author's notebook component maps

2026-09-29. Recovery source map, not a completed recurrence proof.
The author redirected the continuation to the photographed one-page
[notebook PDF](</home/paxinum/Dropbox/Apps/Overleaf/LLT flip/llt pics.pdf>).
It is distinct from the later two-page `dn-local-cases.pdf` produced during
the proof search. The notebook was missing from both recovery handoffs.

We have visually inspected the original. It shows three output diagrams
labelled I, II, III, an `Id map` bracket under II and III, an all-selected
row, and two rows with a shaded row/column interchange and a poset-isomorphism
annotation. The red brackets at the bottom refer to whole components
[theta] and [theta']. The reconstruction below identifies the top row with
relation (8') in the archived author sketch. Its plus sign follows from
two corner splits and DN; it does not rely on reading the overwritten ink.

We use the component maps as the organizing argument: separate the pieces
handled by the identity map, transport the remaining pieces, then check
that the output pieces form complete components. A pointwise poset
identification establishes the valuation identity, while component closure
requires checking flips at the boundaries of the displayed pieces.

## The identity map at a natural corner

Let D be any ordinary decorated natural diagram and let c be a maximal
natural edge that is not marked strict. Write D-c for deletion of c and
D^c for marking c strict. We keep every other decoration and exterior edge.

**Lemma.** The absent-c complete components of D are exactly the complete
components of D-c, under the identity map on selected relations. The
selected-c complete components of D are exactly those of D^c, under the
same identity map. No saturation assumption is needed.

A flip exchanges the two short edges of a natural triangle. The maximal
edge c cannot be a short edge, since it would then be properly contained
in the natural long edge. Its selected status is therefore invariant under
every flip. On the absent stratum c cannot retain a flip either, so deleting
it changes neither a selected relation nor any adjacency. On the selected
stratum marking c strict prohibits no exchange that was previously possible;
the full flip graph again remains identical. This proves both assertions,
including connectedness and completeness with arbitrary exterior.

Both maps preserve the full selected relation, hence the strict-coloring
valuation K and the HRV elementary valuation E. If normal selected edges
carry weight t, marking the selected c removes exactly one such edge.
Its original weighted contribution is t times its marked contribution.
Thus, for either weighted valuation,

    X_D = X_(D-c) + t X_(D^c).

This identity holds component by component on its two invariant strata.
In the notebook, II and III are respectively the absent-e and selected-e
strata AFTER deleting e'. They occur with a plus sign. Both maps are
identities on whole components, with a factor t on the marked stratum.

Related existing argument: the corner resolution in
[flip-component induction](FLIP_COMPONENT_INDUCTION.md), and the absent
normal-corner deletion in [joint DN repairs](COMPONENT_DN_JOINT_REPAIRS.md).
This section makes that argument explicit for the recovered sketch; it
does not supply the remaining DN reassembly.

## Reconstructing the top row

Use the DN notation of the next section. We write S for the common strict
edges, and suppress the common exterior natural edges in this table.

| Notebook diagram | Local natural edges | Local strict edges |
| --- | --- | --- |
| D0, on the left | e,e',q,r | r |
| I | e,f,q,r | e,f |
| II | q,r | r |
| III | e,q,r | e,r |

The blue lower cells of D0 are e' and e, and the blue diagonal cell is q.
In I the upper blue cell is r and the upper strict cell is f. In the
earlier archived notation, I=D1, II=D3 and III=D2:

    D0=Un.neVe.dW,    I=Ud.nVd.eW,
    II=Uen.nVe.dW,    III=Ud.nVe.dW.

The archived source is `archive/2026-09-27-before-finite-proof/main.tex`
in the Overleaf folder, the commented subsection on relation (8'). Its
pointwise middle-state claim is explicitly marked false there; we use
its diagram labels, not that claim, in this reconstruction.

Let R be D0 with e' marked, and let B=D0-e'. The remaining e is a
natural corner in B. The two proved corner splittings give

    F(D0)=F(B)+t F(R),       F(B)=F(II)+t F(III).

The aggregate DN identity is F(R)=F(I). Therefore the top row reads

    F(D0)=t F(I)+F(II)+t F(III).                     (N1)

These equations hold both for the coloring valuation and for the HRV
valuation, with the normal-selection weight t. For a single component
of D0, we can already finish the e'-absent part of the top row: its e
status is fixed after deleting e', so it is exactly one whole component
of II or III. The selected-e' part is a whole component of R. Transporting
that individual component to I is REVERSE DN, and requires reassembly.

For U=n, V empty and W=e, the natural edge lists in the table are exact
on vertices (u,w,x,z)=(0,1,2,3). In particular, II has vertex 0 isolated.
This checks the deletion of both lower cells in the reconstruction.

## The two endpoint maps in the DN notation

We use u<w<x<z, x=w+1, and the edge names from
[direct DN transport](COMPONENT_DN_DIRECT_OVERLAPS.md):

    e=uw, f=wz, q=wx, r=xz, e'=ux,
    Lij(Q)=Q+e+f+i q+j r,
    Rij(Q)=Q+e'+r+i e+j q.

Read from the R side to the L side, the standard endpoint identifications
matching the all-selected and empty-short pictures are

    R11(Q) -> L11(Q),
    R00(Q) -> L00(sigma Q),       sigma=(w x).

For the first map, both relations have the same closure: e,q,r give the
chain u<w<x<z, and e',f are redundant. For the second map, relabel the
entire exterior together with w,x; e',r become e,f. The ordinary eligible
DN geometry supplies the required equality of the exterior natural-edge
sets. Since x has the outgoing edge r, w,x are not both sinks, and the
adjacent relabelling preserves the order of the sinks. Thus both endpoint
maps preserve K and E. Their inverses are explicit.

These statements concern the indicated strata. A component can leave a
stratum through a flip, so the maps alone do not yet identify its complete
image. That is the role of the notebook's lower component brackets.

We keep the two middle states together through the two local diamonds:

    [R10(Q)]+[R01(Q)] = [R00(Q)]+[R11(Q)],
    [L10(Q)]+[L01(Q)] = [L00(Q)]+[L11(Q)].

The empty-short endpoint swaps the exterior; the full endpoint does not.
The middle component calculation must respect this distinction and match
any additional pieces it introduces. These are the same local diamonds
already used in the direct transport note, not a new coefficient formalism.

## An exact reverse-DN split for one component

Let h be the indicator of one complete R component and write
hij(Q)=h(Rij(Q)). More generally, h may be any integer function constant
on R components. Define

    delta(Q)=h01(Q)-h10(Q),
    l00(Q)=(h00+h10)(sigma Q)-h10(Q),
    l10(Q)=l01(Q)=h10(Q),       l11(Q)=h11(Q).

For X=K,E, the reverse split is

    X_R(h)=X_L(l)+sum_Q delta(Q) X_H(Q+q+r).          (N2)

Here H has natural graph R-e'=L-f, with only S marked strict, as in
the direct DN note. This formula keeps every exterior selection Q.

To prove it, suppose e' covers in R01(Q). The adjacent short q covers,
so the e'-retained exchange q to e is actual and h01(Q)=h10(Q).
Otherwise e' is redundant in R01(Q), and deleting it preserves both
valuations. Thus the unmatched contribution is always

    delta(Q) X_R(R01(Q))=delta(Q) X_H(Q+q+r).

Pair the two R middle states with coefficient h10(Q), and use their
diamond. We obtain coefficients h00+h10 at R00 and h11+h10 at R11,
together with this deletion term. Apply the two endpoint maps, swapping
Q only at 00, and then the L diamond. The resulting four coefficients
are exactly l00,l10,l01,l11. This proves (N2) without the completed
component theorem or any component-balance assumption.

The coefficients l and delta need not yet be constant on whole output
components. Equation (N2) is a valid initial split, not a completed
component recurrence. It specifies the residual for the direction actually
used in the notebook; the forward split has a different residual.

## The middle row cannot be a pointwise poset map

On the four vertices above, R01(empty) has selected edges {02,12,23},
whereas L10(empty) has {01,12,13}. Their HRV partitions are respectively
(4) and (3,1). Their coloring enumerators differ as well: the coefficient
of x_1^2 x_2 x_3 is one for the first poset and zero for the second.
The proposed individual middle-state swap cannot be used as a proof.

The paired map does work here. Each diagram has exactly three components:
the 00 singleton, the two-state middle component, and the 11 singleton.
For the middle components the diamonds and endpoint maps give

    X_R(R10+R01)=X_R(R00)+X_R(R11)
                =X_L(L00)+X_L(L11)=X_L(L10+L01).

The endpoint posets are respectively a three-vertex chain plus an isolated
vertex, and a four-vertex chain. Hence the middle component has coloring
sum e_(3,1)+e_4, exactly its HRV sum. The two singleton components have
coloring sums e_(3,1) and e_4. This proves the complete selected-e' sector
on four vertices. The absent-e' sectors are unions of chains and are
already handled by the identity maps. Thus the entire smallest instance
of the notebook recurrence has a component proof, using the paired row.

## Direction and the induction order

We must distinguish the unmarked source D0 from its selected-corner
representation R. Write A for the number of natural edges, s for the
number of strict edges, B=2A-s for doubled decorated area, and
M=sum_j j*a_j. The changes from D0 in (N1) are

| Output | Change in A | Change in s | Change in B |
| --- | ---: | ---: | ---: |
| I | 0 | +1 | -1 |
| II | -2 | 0 | -4 |
| III | -1 | +1 | -3 |

So (N1) decreases B. But marking e' has ALREADY decreased B by one
when we pass to R. The subsequent R-to-I DN move preserves B and
increases M by z-x. It is not a decreasing step in the forward-DN
order from the main outline. We cannot normalize D0 to R and then
count the earlier marking again as a decrease of the DN step.

A proof using only reverse neutral DN moves may instead order those
moves by n(n-1)(2n-1)/6-M, since 0<=a_j<=j and therefore
0<=M<=sum_(j=0)^(n-1) j^2=n(n-1)(2n-1)/6.
This observation does not supply recurrence coverage or component
reassembly. In particular, we must not alternate the forward and reverse
neutral moves under one claimed monotone moment.

The top-row transcription and the two identity sectors are settled.
What remains is a general collection of (N2), or the forward direct
split, into whole components, followed by a consistently directed
recurrence induction. The retained-edge repairs give some of the required
boundary comparisons; they do not finish that collection.

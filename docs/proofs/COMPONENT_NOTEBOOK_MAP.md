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
[theta] and [theta']. The exact unlabelled cells and the sign before III
still need a checked transcription; we do not infer a new recurrence from
an uncertain reading of that sign.

We use the component maps as the organizing argument: identify the pieces
cancelled by the identity map, transport the remaining pieces, then check
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
In particular, whenever the notebook's II and III differ precisely by this
corner marking, II - t III cancels complete selected-c components. The
remaining absent-c components are whole components of the smaller diagram.
There is no retained-edge repair to prove for that cancellation.

Related existing argument: the corner resolution in
[flip-component induction](FLIP_COMPONENT_INDUCTION.md), and the absent
normal-corner deletion in [joint DN repairs](COMPONENT_DN_JOINT_REPAIRS.md).
This section makes that argument explicit for the recovered sketch; it does
not claim that all its unlabelled cells have already been identified.

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

## Continuation from the sketch

First identify the exact natural graphs and strict corners of I, II, III
in the photograph, keeping uncertain signs explicit. Apply the corner
identity map to the pieces to which it actually applies. Then follow one
complete component through the two endpoint maps and the middle diamonds,
using the red component brackets as the boundary check. The retained-edge
repairs are available when that check reaches one of their stated local
configurations; their unrestricted extension is not a prerequisite for
transcribing or checking the other maps.

The recovered proof increment is `c9c0e3a`, pushed to main. It preserves all
pre-crash edits and adds five conditional arbitrary-exterior repairs in
[the retained-edge note](COMPONENT_DN_RETAINED_EDGE.md). Neither that increment
nor this source map finishes the requested component recurrence. No Lean,
Lake or manuscript build, new worker, or consultant restart was used.

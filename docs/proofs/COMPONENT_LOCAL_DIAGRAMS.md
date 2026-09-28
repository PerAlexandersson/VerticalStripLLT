# Recurrence vertices and an overlapping flip

2026-09-28. We organize the requested component proof by small diagrams:
the vertices of a recurrence together with those of one target flip.
The aim is to collect complete smaller components by proving that the
corrected coefficient is unchanged across each target flip. We retain the
entire exterior selection throughout each local argument.

## The two NN pictures

Write a<b=a+1<c, with strict corner ac, and delete ac for the target.
Put q=ab and r=bc. The proved
[NN overlap classification](COMPONENT_NN_OVERLAPS.md) shows that the
uncorrected coefficient is already constant across every flip preserving q.
Only the following pictures remain:

| Ordered vertices | Recurrence triangle | Flip triangle | Retained edge | Exchanged edges |
| --- | --- | --- | --- | --- |
| t<a<b<c | abc | tab | tb | ta,ab |
| a<b<d<c | abc | abd | ad | ab,bd |

Each picture has four vertices. This classification holds with the full
exterior present. It is stronger than an enumeration of isolated diagrams.
The completed [unicyclic NN proof](COMPONENT_NN_LEFT_REASSEMBLY.md)
repairs these two comparisons. Its auxiliary paths may use more vertices
than the four displayed in the initial overlap.

## Why five vertices are a natural next bound

The DN recurrence uses u<w<x<z, with x=w+1. Its source strict edges
are uw,wz; its target strict edges are ux,xz. A flip has three vertices.
If its triangle shares an edge with this four-vertex set, their union has
at most five vertices. We can therefore draw every such overlap using the
four recurrence vertices and at most one additional vertex t.

The target variable edges are p=uw and q=wx. Every flip exchanging p
exchanges it with q, so its triangle is uwx. A flip exchanging q has
triangle twx or wxt; this adds at most one vertex to the recurrence.
Thus every flip changing the target (p,q) sector is a five-vertex case.

A flip preserving p,q may share just one recurrence vertex, or none,
so its union with the recurrence can have six or seven vertices. The lifting
lemma below handles these flips with the full exterior present. It gives
a five-vertex reduction for all target comparisons once the source
multiplicities have been balanced.

## What each diagram must assert

We draw the recurrence horizontally and the target flip vertically. The
other side of the square is a source flip path, or a diamond identity
with an explicitly displayed correction. The purpose of the square is
to prove equality of the two target coefficients.

We keep three pieces of information beside the picture:

- which edges are selected, absent, or strict;
- which edges must be covers in the full orientation;
- the correction, if any, and its identical effect on the coloring and
  HRV sums.

An exterior directed path can make a displayed edge redundant. Consequently
an isolated five-vertex calculation does not by itself justify the same
picture inside a larger diagram. We must either prove that the needed
covers follow from the given actual flip, or display the path condition
under which a different diamond applies. The NN classification already
provides an example of doing this with arbitrary exterior selections.

## DN middle flips away from the new strict edge

We can now remove the apparent six- and seven-vertex middle comparisons. This argument
uses the eligible ordinary DN geometry, but does not require saturation or
a bound on cycle rank.

Write e=uw, f=wz, e'=ux, q=wx and r=xz. The exterior selection Q includes
the unchanged strict edges. Our source and target middle states are

    L01(Q)=Q+e+f+r,
    R10(Q)=Q+e'+r+e,       R01(Q)=Q+e'+r+q.

**Lemma.** Suppose an actual target flip preserves p=e and q, and its
retained long is not e'. If it joins R10(Q),R10(P), or R01(Q),R01(P),
then the same exterior exchange is an actual source flip joining
L01(Q),L01(P).

**Proof.** In an ordinary diagram, inserting or removing a maximal natural
edge cannot change the cover status of another natural edge. A path using
the changed edge would have endpoints whose interval contains that edge,
contradicting maximality unless it is the changed edge itself.

For R10 we delete the target-maximal edge e' and insert the source-maximal
edge f, at both endpoints. Neither is tested by the given flip. All its
required edges and covers therefore survive, giving the claimed L01 flip.

For R01 we first insert e. The only target natural edge properly containing
e is e', so only its cover can change. The given flip does not test e',
and therefore lifts to R11. Both R11(Q) and L11(Q) have the transitive
closure of Q+e+q+r: e' is implied by e,q, and f is implied by q,r.
Thus the tested common edges have the same covers, and the exchange gives
an L11 flip. Finally we delete q at both endpoints. It is not exchanged,
and adjacency prevents it from being the retained long. Deleting it can
only remove bypasses, so all required covers survive. We obtain the L01
flip. The exchanged edges remain normal in the source: they are common
exterior normals, not the source-strict edge e. This proves the lemma.

For any source multiplicity h constant on complete components, the lemma
gives h01(Q)=h01(P). In the direct DN transport the rank-safe choice of
middle coefficients is g10=g01=h10. If we have already repaired h so that
h10=h01, every comparison in the lemma is consequently settled.

The remaining middle flips retain e'=ux. Their triangle is u<t<x.
If t=w, this is the internal R10(Q)<->R01(Q) flip, and its coefficients
agree by definition. Otherwise adjacency gives u<t<w<x<z: the recurrence
and the exceptional flip use exactly five vertices. This proves the
five-vertex reduction for middle comparisons after balance. Lower and upper
mixed comparisons remain separate, as do the construction of a balanced
repair for an arbitrary component and compatibility of its correction terms.

## All target comparisons after balance

**Proposition.** Let h be constant on source components and satisfy
h10(Q)=h01(Q) for every Q. Define the DN target coefficients by

    g00(Q)=(h00+h01)(sigma Q)-h01(Q),
    g10(Q)=g01(Q)=h01(Q),       g11(Q)=h11(Q).

Every target flip preserves g except possibly a flip retaining e' or
exchanging q. Each of these remaining comparisons involves at most five
vertices together with the recurrence vertices.

**Proof.** Full-sector flips preserve h11 by the full-stratum closure
identification. The preceding lemma settles middle flips not retaining e'.
The internal middle flip preserves g by its definition.

Consider a target 00 flip not retaining e'. Insert p=e at both endpoints.
Only e' could acquire a bypass, since it is the only target natural edge
properly containing e. Such a bypass would use a w-to-x path; this is
impossible because q is absent and x=w+1. Thus the flip lifts to R10,
and the lemma gives h01(Q)=h01(P).

The zero-stratum swap identifies the original target 00 flip with a source
00 flip on sigma Q,sigma P. Adding r preserves this source flip: the only
natural edge properly containing r is f, and a bypass of f through r
would again need the absent q. It follows that both h00 and h01 agree on
sigma Q,sigma P. This proves constancy of g00.

Every flip changing p exchanges it with q and retains e', so it is the
already settled internal middle flip. All other sector-changing flips
exchange q. Their triangle contains w,x and one more vertex. A flip
retaining e' has triangle u,t,x. Either triangle adds at most one vertex
to u,w,x,z, proving the asserted bound.

The proposition reduces coefficient comparisons; it does not construct
balanced source multiplicities starting from a single component. Once a
correction supplies balance, the remaining tasks are precisely the displayed
overlaps, with their full exterior cover conditions.

Primary and the existing independent Astra reviewer checked the lemma,
proposition, normality and the full exterior cover tests. No finite computation
or previously completed component formula is used in this proof.

## Shared diagram conventions

The user requests the same cell notation for the circular aggregate HRV
proof. We inspected Examples 4.1 and 5.3 of the Alexandersson--Sulzgruber
paper (published pages 21 and 27): vertex labels occupy yellow diagonal
cells, off-diagonal cells encode pairs, and gray cells carry no ascent
weight. An arrow in a gray cell specifies a strict edge; a gray empty
cell excludes the pair. A white empty cell leaves an ordinary edge
unspecified. Arrows and dots can then refine the sums, with their precise
weight convention stated where the refinement is used.

The circular bounce pictures use ordered integer lifts as their diagonal
labels and denote the corresponding periodic local change. A cell picture
does not license discarding exterior paths or cyclic cases. The circular
triangle identity and periodic HRV comparison remain the justification.

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

This is not yet a five-vertex theorem for all coefficient comparisons.
A flip preserving p,q can meet the recurrence vertices only at w or x,
and hence its union with the recurrence can have six vertices. Such flips
must be shown to commute with the transport, or reduced to the preceding
cases. The existing source/target 00 lifts settle some comparisons, but
do not on their own prove every DN middle-sector comparison.

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

The next proof task is the DN comparison for flips preserving p,q:
separate the commuting cases from those requiring a shared-edge repair.
This tests the proposed five-vertex organization before expanding a case
table or moving it into the manuscript. No general five-vertex reduction
or general DN component recurrence is claimed here.

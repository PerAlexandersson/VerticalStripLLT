# Joint DN repairs in the five-vertex pictures

2026-09-28. We give identities which move terms between the DN target
and the corner-deletion diagram. In the smallest right-hand picture,
one such identity completes both images for every source component.
For a general diagram, compatibility of all corrections remains open.

We use the notation and direct transport of
[Direct DN overlaps](COMPONENT_DN_DIRECT_OVERLAPS.md). Thus

    u<w<x<z,   x=w+1,
    e=uw, f=wz, q=wx, r=xz, e'=ux,
    Lij(Q)=Q+e+f+i q+j r,
    Rij(Q)=Q+e'+r+i e+j q.

The source has strict e,f; the target R has strict e',r. The deletion
diagram H has neither pair marked strict. Common strict edges remain in Q.
An expression such as H(Q+e+a) specifies its entire selected relation.
We write diagram terms for either valuation X=K or X=E. Every identity
below has the same coefficients for these two valuations.

For a component-constant integer function h, direct transport gives

    X_L(h)=X_R(t)+sum_Q delta(Q) X_H(Q+e+q),
    delta=h10-h01,
    t00=(h00+h01) composed with sigma - h01,
    t10=t01=h01,   t11=h11,

where sigma exchanges adjacent vertices w,x on the whole exterior.

## The right-hand picture

Let u<w<x<t<z, and put a=wt, b=xt, c=tz. In this section Q omits
these three edges as well as the recurrence edges. It can contain any
selection of the remaining exterior edges, including all common stricts.

The basic identification is

    R00(Q+a+b+c) = H(sigma Q+e+a+b+c).                 (1)

Indeed, r is redundant through b,c on the left. Delete r and exchange
w,x: e' becomes e, a and b exchange, and c is fixed. This preserves the
coloring sum by relabeling vertices. It also preserves the HRV partition:
both w,x have outgoing edges to t, so neither is a sink; the adjacent
exchange preserves the order of every sink. Thus (1) holds for both X.

Two diamonds give the further identity

    R00(Q+a+b)+R00(Q+a+c)+H(sigma Q+e+a+q+c)
      = R00(Q+a)+H(sigma Q+e+a+c)+H(sigma Q+e+q+b+c).  (2)

First apply the diamond retaining r, with shorts b,c and a fixed. Its
full term is the left side of (1). After (1), apply the diamond retaining
a with shorts q,b and with e,c fixed. In its full term a is redundant
through q,b, giving exactly (2). These valuation diamonds do not require
the displayed edges to be covers in the full exterior.

## A complete repair on five vertices

Take the source area sequence (0,1,1,2,3), with vertices
(u,w,x,t,z)=(0,1,2,3,4). Its natural edges are precisely
e,f,q,r,a,b,c, and only e,f are strict. The target has area
(0,1,2,2,2), and H has area (0,1,1,2,2).

Put

    U=R00(a+b+c),   V=H(e+a+b+c),
    d=h01(a+c)-h00(a+b+c).

**Proposition.** For every component-constant integer function h on this
source, add d to the direct coefficient of U and subtract d from that
of V. The resulting coefficients are constant on every complete component
of R and H. Consequently direct transport becomes an identity in whole
smaller components, with identical integer coefficients for K and E.

**Proof.** The correction has zero valuation by (1). The direct-overlap
theorem already settles all comparisons except flips exchanging q in the
triangle w,x,t. There is no left-hand picture in this diagram.

For target comparisons with e selected, the actual flip lifts to the
source, giving h11(a+B)=h01(a+b+B), where B is empty or {c}.
For e absent and c absent, the only remaining comparison is
R01(a) with R00(a+b). Their coefficients are h01(a) and h00(a+b),
since sigma fixes a+b. The actual source path

    e+f+a+r <-> e+f+a+q <-> e+f+a+b

first retains f, then a. Thus h01(a)=h10(a)=h00(a+b).
This also proves delta(a)=0 for the corresponding H comparison.

With c selected, the target comparison is R01(a+c) with U, whose
coefficient difference is d. The actual source flip

    e+f+q+a+c <-> e+f+a+b+c

retains a and gives h10(a+c)=h00(a+b+c). Hence delta(a+c)=-d.
The H comparison is H(e+q+a+c) with V; its coefficients are -d and zero.

Finally U has only one actual neighbor, R01(a+c), and V has only one
actual neighbor, H(e+q+a+c). Adding d at U and -d at V therefore closes
both comparisons and changes no other boundary. This proves the claim.

For example, the following complete five-state source component

    C={e+f+B : B in {q+a+b, q+a+r, a+b+r, a+r+c, b+r+c}}

has d=1. Its repaired identity is

    X(C)=X(D6)+X(D2)-X(T2)-X(T1),

with the following complete components:

    D6={R11(a), R10(a+b), R01(a+b),
        R10(a+c), R01(a+c), R00(a+b+c)},
    D2={R10(b+c), R01(b+c)},
    T2={H(e+q+a+c), H(e+a+b+c)},
    T1={H(e+q+b+c)}.

The direct expression lacks one member of D6 and one member of T2.
The single zero relation U-V supplies both, with the required signs.

## The left-hand picture

Let u<t<w<x<z, and now put a=ut, b=tw, c=tx. Again Q omits all
displayed local edges. Two identities with arbitrary exterior are

    R10(Q+a)+R10(Q+c)+H(Q+e+r+b+c)
      = R10(Q)+H(Q+e+r+c)+H(Q+r+a+b+c),              (3)

    R00(Q+a+b)+R00(Q+b+c)+H(Q+e+r+c)
      = R00(Q+b)+H(Q+e+r+a+c)+H(Q+e+r+b+c).        (4)

For (3), apply the e'-diamond with shorts a,c, keeping e,r. Delete
redundant e' in its full term, to obtain H(Q+e+r+a+c). The e-diamond
with shorts a,b and with r,c fixed gives (3), after deleting redundant
e from its full term. For (4), apply the e'-diamond with b fixed;
its full term becomes H(Q+r+a+b+c). Expand this by the same e-diamond.

All H terms in (3)--(4) select r. Thus these identities alone do not
repair the initial r-absent deletion coefficients. We must match the
terms introduced by different corrections as well.

## What remains after the right-hand correction

Here we return to a=wt, b=xt, c=tz and allow exterior Q. Put S=h00+h01.
For an actual target comparison R01(Q+a+c)<->R00(Q+a+b+c), the defect is

    d(Q)=h01(Q+a+c)+h01(Q+a+b+c)-S(sigma Q+a+b+c).

The same a-retained flip lifts to
L10(Q+a+c)<->L00(Q+a+b+c), so

    d(Q)+delta(Q+a+c)=S(Q+a+b+c)-S(sigma Q+a+b+c).

Adding d(Q) copies of (1) fixes this target comparison. Apply the correction
once at each distinct background in {Q,sigma Q}. The corresponding H
comparison then has remaining coefficient difference

    k(Q)=delta(Q+a+c)+d(sigma Q)
        =h01(sigma Q+a+c)+h01(sigma Q+a+b+c)
          -h01(Q+a+c)-h01(Q+a+b+c).

In particular k(sigma Q)=-k(Q). These formulas apply when the displayed
comparisons and their reflected counterparts are actual. They do not
assert that the corrections preserve all other comparisons.

This identifies the next terms to match. The local set a+b+c is fixed
by sigma. The moved exterior pairs are incoming vw,vx with u<v<w, or
outgoing ws,xs with x<s<z. Thus the remaining difference involves the
left-hand picture and other occurrences of the right-hand picture.
We can telescope an exterior swap into these pairs algebraically, but
an individual pair replacement need not be an actual flip. Turning
that telescoping into joint diamond corrections is still required.

## Transferring through a longer bypass

We can strengthen (1). In the right-hand notation a=wt, b=xt, c=tz,

    R00(Q+b+c)=H(sigma Q+e+a+c).                       (5)

The extra arm a on the left of (1) is unnecessary. The DN bottom
identification gives R00(Q+b+c)=L00(sigma Q+a+c). In this source
term f is redundant through a,c; deleting f gives (5).
More generally, whenever r is redundant in R00(Q),

    R00(Q)=H(sigma Q+e).                              (6)

An alternative path from x to z in Q swaps to a path from w to z
in sigma Q, so f is redundant in L00(sigma Q). This proves (6)
directly from the same DN bottom identification. Equivalently, delete r
and swap w,x. In this argument x is a nonsink; the adjacent swap therefore
preserves the relative order of the sinks, even if w itself is a sink.

There is a useful difference identity for the exterior pairs in k(Q).
Let ell,s be respectively the long and the other short edge in either
triangle v<w<x or w<x<v, with q=wx as the remaining short. For any
common selected background Z omitting q,ell,s, the diamond gives

    H(Z+q+ell)-H(Z+q+s)=H(Z+ell)-H(Z+ell+s).           (7)

In its full term ell is redundant through q,s. Thus (7) moves the
difference between the two q-selected states into two q-absent states,
without an actual-cover assumption.

Suppose v differs from the right-hand vertex t and that we retain e,a,c.
Combining (7) with (5) gives

    H(Q+e+a+c+q+ell)-H(Q+e+a+c+q+s)
      =R00(sigma Q+b+c+s)-R00(sigma Q+b+c+ell+s).      (8)

Here sigma exchanges ell,s; Q omits all displayed local edges. Incoming
and outgoing pairs are both allowed. Consequently a telescoped exterior
swap can be transferred back to target 00 terms with r redundant.
These are explicit zero relations for the remaining differences. We
still have to choose their coefficients compatibly over whole components.

### Shortening a bypass by diamonds

Long paths in (6) do not require a new identity for every length.
Suppose a selected bypass is v0->v1->...->vm, m>=3, inside a natural
strict corner. Put a0=v0v1, b0=v1v2 and g=v0v2. All three edges are
normal because their intervals lie properly inside that corner.
If g is absent, then

    X(Z+a0+b0)
      =X(Z+g+a0)+X(Z+g+b0)-X(Z+g).                   (9)

Indeed, insert redundant g into the left side and use its diamond.
Each right-hand term retains the shorter path v0->v2->...->vm.
If g is already present, simply choose that shorter path. Applying
this to a shortest selected bypass decreases its length on every branch.
Iteration terminates with two-edge bypasses and integer coefficients.

We can use the same expansion on both sides of a cross-diagram identity.
For redundant e', apply identical triangles in R and in H after deleting
e'; all the shortcut edges are common. At each leaf, e' is redundant
through a two-edge path. For (6), apply the triangles on the x-to-z
path in R and their sigma images on the w-to-z path in H. The common
coefficients are +1,+1,-1, and each leaf is an instance of (5).
Thus the longer bypass identities follow constructively from ordinary
diamonds, redundant-edge deletion and the two-edge cross identifications.

A triangle used along a bypass can contain two vertices outside the
original recurrence. Its union with the original four vertices can then
have six vertices. We use successive local diagrams; we do not require
every subsequent diamond to stay inside one fixed five-vertex set.

### Two right-hand exits from one orientation

There is already a local consistency statement for choosing correction
coefficients. Suppose R00(Q) has actual q-changing flips at both triangles
w,x,t and w,x,s, with t!=s. Put a_t=wt, b_t=xt and similarly a_s,b_s.
All four edges belong to Q. The two q-selected target neighbors carry
source coefficients h01(Q-b_t) and h01(Q-b_s). These are equal.

Indeed, put Q'=Q-b_t-b_s. We have the actual source path

    L01(Q-b_t) <-> L11(Q') <-> L01(Q-b_s).            (10)

The first flip retains a_s and replaces b_s by q; the second retains
a_t and replaces q by b_t. For the first, the required covers survive
deleting b_t and replacing e' by e,f. For the second, q covers because
it is adjacent. A new bypass of a_t would have to use q and then an
x-to-t path in Q', contradicting the cover of b_t in the original target.
The edges e,f,r cannot affect these paths: e is upstream, and f,r end
at z>t,s. The exchanged shorts are normal inside the source corner f.
This proves (10) and the equality of coefficients.

Thus a correction at one 00 orientation is independent of which right-hand
exit we use to specify its coefficient. We still need consistency along
paths of 00 orientations and at the left-hand overlaps.

## Verification and remaining work

The proposition has a direct cover-and-coefficient proof above. An
independent Astra reviewer checked its signs, all actual flips and the
absence of additional neighbors. Exact enumeration also checks the
original transport, the zero correction, complete output components and
both valuations for all 15 source components. Only two components need a
nonzero correction: the displayed five-state component has d=1, and
{e+f+a+b+c, e+f+q+a+c} has d=-1.

The arbitrary-exterior identities (2)--(4) were derived independently.
Exact checks include 16 exterior selections of a six-vertex right-hand
example and eight selections of a six-vertex left-hand example, the latter
including a common strict edge. These checks support the algebraic proofs;
they do not establish general component constancy after correction.

Related Rust: the external `hrv-bridge/src/bin/dn_joint_matching.rs` consumer
reuses `nn_component_transport::{components, valuations}` and
`component_source_probe::{make_model, flip}`. Its frozen source, dependencies,
run logs and checksums are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-joint-five-vertex/`.
No Lean source or build is involved in these new identities.

A subsequent exact span calculation retains the full target and H state
spaces. Its generators are ordinary diamonds, deletion of a normal edge
made redundant by a two-edge path, deletion of e' through a two-edge path
from R to H, and (6). We also include the indicator of every complete
component of R and H. We assemble the original direct image of each source
component and test membership in this rational span. No equality for a
whole component is assumed when constructing the zero relations.

The diamonds and within-diagram normal deletions in this test use at most
one vertex outside {u,w,x,z}; relation (6) allows a longer bypass and has
the constructive reduction (9).

| Source area | Strict edges | Source components | Images outside the span |
| --- | --- | ---: | ---: |
| 01123 | 01,14 | 15 | 0 |
| 01222 | 02,24 | 14 | 0 |
| 011234 | 01,15 | 116 | 0 |
| 012233 | 02,14,25 | 26 | 0 |
| 0122332 | 02,14,25,46 | 28 | 0 |
| 0112343 | 01,15,36 | 177 | 0 |

These are six selected diagrams, not an exhaustive scan through seven
vertices. If we restrict (6) to two-edge bypasses in the same test, six
source images of 011234 remain outside the span. Allowing either the long
bypass transfer or ordinary exterior triangles and their normal deletions
resolves these six. Thus the path-shortening step has a concrete role.

For the two-state source component in 011234,

    C={01+15+12+13+34+45, 01+15+13+23+34+45},

the direct image is H(01+12+13+34+45)+R00(13+23+34+45).
The one instance of (6)

    R00(13+23+34+45)=H(01+13+23+34+45)

completes the two-state H component. Its bypass 2->3->4->5 has length
three. The exact certificate contains only this zero relation and the
whole H component. A 34-state source component in the same diagram also
has a checked integral certificate, with 101 zero-relation terms and eight
whole output components. Every certificate equation, each used zero
relation, and both final valuations were checked exactly. The automatic
certificate is not yet an expository proof of the general construction.

Related Rust: `hrv-bridge/src/bin/dn_joint_span.rs` reuses
`sym_poly_core::sparse_linear_algebra::{SparseQuotientSpace, sparse_rref}`
and the same component/valuation APIs. Frozen sources, explicit commands,
logs and checksums are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-joint-span/`.
All-case span membership is over the rationals; integrality is asserted
only for the two explicit certificates just described.

For general DN, we still need to choose the coefficients of joint repairs
so that all component boundaries close simultaneously, including exterior
flips and the left-hand picture. This note settles the complete minimal
example and supplies identities for the general matching; it does not
claim that this last compatibility step, or the other recurrences, is done.

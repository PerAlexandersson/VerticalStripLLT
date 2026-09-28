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

For general DN, we still need to choose the coefficients of joint repairs
so that all component boundaries close simultaneously, including exterior
flips and the left-hand picture. This note settles the complete minimal
example and supplies identities for the general matching; it does not
claim that this last compatibility step, or the other recurrences, is done.

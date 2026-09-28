# Joint DN repairs in the five-vertex pictures

2026-09-28. We give identities which move terms between the DN target
and the corner-deletion diagram. In the smallest right-hand picture,
one such identity completes both images for every source component.
For a general diagram, compatibility of all corrections remains open.

The [source-addition continuation](COMPONENT_DN_SOURCE_ADDITIONS.md) proves
a six-vertex recurrence by adding two deletable components. It also records
exact source-addition checks beyond the minimal diagrams.

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

### A complete component recurrence for the left-hand diagram

Consider the source area (0,1,2,2,2), with
(u,t,w,x,z)=(0,1,2,3,4). The strict edges are e=02 and f=24;
the normal edges are a=01, b=12, c=13, q=23, r=34.
The target area is (0,1,2,3,1). We also use the smaller diagram J
of area (0,1,2,1,2), obtained by deleting the unmarked natural corner c;
its strict edges remain e,f. This additional deletion diagram makes
the component recurrence considerably shorter than a repair confined to R,H.

There are five source components with c selected:

    C_k={e+f+c+B : B subset {a,b,q,r}, |B|=k},  0<=k<=4.

Indeed, flips retaining e,c,f exchange adjacent unequal bits in the
word (a,b,q,r). Their covers impose exactly the condition that one of
the exchanged edges is selected. Thus C_k is a complete component of
size binomial(4,k).

With c absent, the flips retaining e and f act independently. The nine
complete components are

    I_ij={e+f+A+B : A subset {a,b}, |A|=i,
                       B subset {q,r}, |B|=j},  0<=i,j<=2.

Each I_ij remains a whole component in J. Deleting an absent natural
corner changes no selected relation or available actual flip, so it
preserves both valuations. This immediately gives a smaller-component
identity for every c-absent source component.

For the c-selected components, the following are exact identities for
both X=K and X=E. Each set displayed in the target column is a complete
component; separate sets are added. The last column is subtracted in J.

| Source | Complete target components in R | Subtract in J |
| --- | --- | --- |
| C_0 | {R00(b)} | 0 |
| C_1 | D_8 | I_11 |
| C_2 | D_5 + D_2 + {R01(a+b)} | I_21 |
| C_3 | {R10(a+b+c),R11(a+c),R11(b+c)} + {R01(a+b+c)} | 0 |
| C_4 | {R11(a+b+c)} | 0 |

Here

    D_8={R00(a+b),R00(b+c),
         R10(a),R01(a),R10(b),R01(b),R10(c),R01(c)},
    D_5={R10(a+b),R10(a+c),R10(b+c),R01(b+c),R11(c)},
    D_2={R00(a+b+c),R01(a+c)}.

**Proof of the identities.** All source middle pairs L10(Q),L01(Q)
are actual flips retaining f: the two shorts q,r are adjacent and f
has no other possible bypass. Thus delta=0 for every source component.
Apply the direct DN formula to C_0,C_3,C_4; its output is precisely
the indicated target sum. For the two remaining cases, apply it to
C_1+I_11 and C_2+I_21. Their target coefficients are respectively
the indicator of D_8 and the sum of the indicators of
D_5,D_2,{R01(a+b)}. Subtract the added I-component in J. This
constructs an identity for one original component, with integer
coefficients and whole smaller components on the other side.

The target component checks are short. D_8 consists of all orientations
with two selected normal edges except the two isolated states
R00(a+c),R11(empty); its remaining eight states are connected by the
displayed triangle flips. D_5 is a four-leaf star centered at R10(b+c).
D_2 is one flip retaining c. The three-state set in the C_3 row is
a path, with center R11(a+c), and its companion is isolated.
All other displayed singleton sets are isolated. These checks also
show that no unlisted orientation belongs to a displayed component.

Thus both minimal five-vertex pictures now have component recurrences.
The left-hand construction uses another smaller corner-deletion diagram;
there is no requirement that every correction end in the original R,H pair.
This proof uses the five-vertex source explicitly. It does not assume that
its component classification persists unchanged with arbitrary exterior.

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

### Propagating a deletion along flips

Fix b_t=xt, x<t<z. Suppose an actual 00-to-00 target flip preserves
b_t selected, does not retain b_t, and does not retain e'. Then deleting
b_t and replacing e' by e,f gives an actual source flip

    L01(Q-b_t) <-> L01(P-b_t).                        (11)

The deleted b_t is neither retained nor exchanged, so all the tested
selected edges remain and their covers survive deletion. Deleting maximal
e' and adding the source natural corners e,f also preserve every tested
cover. Apply this at both endpoints to obtain (11).

Consequently this source component label propagates along any such target
path. Intermediate orientations need not have a right-hand q-exit: a_t
may be absent or may cease to cover, and b_t may itself become redundant.
Losing an available exit is therefore not, by itself, an obstruction.

When w=u+1, a 00 flip cannot retain e': its only interior vertex is w,
and both corresponding shorts are absent. At a 00 orientation with b_t
selected, the exceptions to (11) are precisely flips in triangles x,s,t
retaining b_t, with x<s<t<z,
or triangles x,t,s exchanging b_t, with x<t<s<=z. The endpoint s=z
is allowed: it is the r-retained flip exchanging xt and tz.
An incoming alternative v,x,t would require v=w, which changes q,
or v<=u, whose long edge vt is excluded by maximality of e'.
These are the remaining cases for propagating this particular deletion;
their general repair is not proved by (11).

### Letting the deleted edge move with the flip

We can handle the exchanged-edge case without an additional diamond.
Let A be a target 00 orientation and g a selected normal edge. Associate
to it the source 01 orientation

    A_g = (A - {e',g}) + {e,f}.

Suppose an actual target 00 flip joins A=Z+ell+a to B=Z+ell+b, retaining
ell and exchanging a,b. There are two immediate cases:

| Edge deleted at A | Edge deleted at B | Source relations |
| --- | --- | --- |
| a | b | A_a=B_b |
| g in Z, with ell different from e' | the same g | A_g and B_g are joined by the same flip |

For the first row, both deletions leave Z+ell before replacing e' by e,f.
This works even when ell=e'. For the second, deleting the two untested
edges g,e' preserves all tested covers. Adding the source natural corners
e,f cannot create a bypass of a tested edge. Thus the same source flip
remains actual. All common exterior edges are retained.

In particular, when a target flip exchanges xt with ts, we delete xt
before the flip and ts afterwards. Both source orientations are identical.
This includes s=z: the flip retaining r and exchanging xt,tz needs no
separate repair. Along a succession of flips we may continue following the
exchanged edge, rather than insisting on deleting the original xt.

The cases still requiring a repair are a flip retaining the deleted edge,
and a flip retaining e' while the deleted edge is unchanged. When w=u+1,
the latter is impossible in 00. This reduces that propagation calculation
to the retained-deleted-edge case; it does not prove its general repair.

The separate Overleaf sheet `dn-local-cases.tex` displays the xt/tz case
in the author's cell notation and illustrates (1)--(2) by deleting the
redundant r and using two diamonds. The existing Astra reviewer checked
the new lemma, all displayed cell indices and the written calculation.

### The retained-edge case on five displayed vertices

Here is the local calculation when the target flip retains the deleted
edge g=xt and exchanges p=xs with j=st, where w<x<s<t<z.
In the source, keep f=wz, r=xz and A=wt selected, with q=wx and g absent
at the two endpoints. The remaining three bits are

    alpha=ws, beta=sz, gamma=tz.

The upstream strict edge e=uw stays selected throughout. First suppose
these are all the vertices between w and z and there are no other selected
edges incident with them. The following eight pairs give sixteen states.
In each row, the displayed sequence replaces p by j, restoring all other
edges. An arrow is an actual source flip; the last column lists its retained
edge. Fixed e,f,r,A are omitted from the states.

| (alpha,beta,gamma) | Selected variable edges along the path | Retained edges |
| --- | --- | --- |
| 000 | p -> beta -> alpha -> j | r,f,A |
| 100 | alpha+p -> p+j -> beta+j -> alpha+j | A,r,f |
| 010 | p+beta -> p+alpha -> p+j -> beta+j | f,A,r |
| 110 | alpha+p+beta -> p+j+beta -> alpha+p+j -> alpha+beta+j | A,f,r |
| 001 | p+gamma -> p+g -> g+j -> j+gamma | r,g,r |
| 101 | alpha+p+gamma -> alpha+p+g -> alpha+g+j -> alpha+j+gamma | r,g,r |
| 011 | p+beta+gamma -> p+j+beta -> alpha+p+j -> alpha+j+beta -> alpha+beta+gamma -> j+beta+gamma | beta,f,r,beta,A |
| 111 | alpha+p+beta+gamma -> q+alpha+beta+gamma -> alpha+g+beta+gamma -> alpha+g+j+beta -> alpha+j+beta+gamma | alpha,A,beta,r |

We can check the covers directly. When gamma=0, retaining r,f,A exchanges
adjacent unequal bits in (p,beta,alpha,j); the first four rows perform
these exchanges. When beta=0 and gamma=1, we replace gamma by g, perform
the original g-retained flip, and replace g by gamma. The last two rows
give the five- and four-flip paths when beta=gamma=1. In every listed
triangle exactly one short is selected, and neither the long edge nor
the selected short has an alternative directed path.

All eight paths also work with any fixed exterior having no directed path
between distinct vertices in {w,x,s,t,z} after the displayed local edges
are removed. Indeed, a bypass that leaves these vertices would have to
return to a different displayed vertex. The hypothesis rules this out,
so every local cover test is unchanged. Branches attached at a single
displayed vertex are allowed.

This proves the local sixteen-state calculation. With unrestricted exterior,
the original target g-flip does not certify the intermediate covers of
f,r,alpha,beta. Those cases still need a diamond repair; the table is not
an arbitrary-exterior component recurrence.

Related Rust: `first_join_tree_lifts.rs --retained-mark-table`, using
`component_source_probe::{component,flip}`, checks all eight pairs in
area011234 with strict01,15 and prints the paths above. The existing Astra
reviewer independently checked all eight local paths and the stated exterior
extension. Sources, logs and review are frozen under the external
`dn-local-cases/` receipt directory.

### Moving obstructing edges aside beneath a corner

The last flip of the 000 row can fail because an exterior path makes A=wt
redundant. We can repair this without a diamond when the outer corner f=wz
still covers. The following statement also allows ws to be redundant.

**Lemma.** Let w<s<t<z lie beneath a natural strict corner f=wz. Suppose
f,wt,ws are selected, f is a cover, and there is no selected directed path
from s to t. Then replacing ws by st, with all other edges restored, gives
an orientation in the same source component.

**Proof.** List the selected edges wv, other than ws,wt, such that v can
reach s or t. Each such v is less than t. In increasing order of v, replace
wv by vz, retaining f. These are normal edges inside f.

Each move is an actual flip. The edge wv is a cover when we reach it: a
bypass would start with wy for y<v, with y also reaching s or t, so wy
would already have been removed. The retained edge ws cannot start such
a bypass, since s cannot reach t (or itself by a nonempty directed path).
The changes into z do not affect any path ending at or before t.
Finally, the cover of f excludes a path from v to z while wv is selected.
After replacing wv by vz, a new bypass of f would require a previously
existing bypass of wv. Thus f and the exchanged shorts have the required
covers at both endpoints.

After these moves, ws and wt both cover. We can perform the flip retaining
wt and exchanging ws,st. It leaves f a cover: a newly created bypass of f
would use st and continue from t to z, but that latter path was excluded
by the cover of f and the selected edge wt.

Now undo the preceding moves in reverse order. Compared with the forward
path, ws is absent and st is present. Deleting ws cannot spoil a cover.
Adding st cannot create a bypass of wv, since v<t, or a bypass of vz or
f, since there is still no path from t to z. All reverse moves are
therefore actual. They restore every edge except for the desired exchange
ws to st. This proves the lemma.

For example, take w<x<y<s<t<z in row000 and add wy,yt to its exterior.
The target flip retaining xt is actual, but wt is redundant through y.
After the first two moves of row000, we use

    wy -> yz [retain f],
    ws -> st [retain wt],
    yz -> wy [retain f].

This gives a five-flip source path with the exterior restored. Neither
strict-corner deletion nor a longer list of orientation cases is needed
for this obstruction. The lemma assumes f covers; it does not settle
the retained-edge case when an exterior path also makes f redundant.
The existing Astra reviewer independently checked the full argument,
including reverse restoration with arbitrary exterior, and the example.

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

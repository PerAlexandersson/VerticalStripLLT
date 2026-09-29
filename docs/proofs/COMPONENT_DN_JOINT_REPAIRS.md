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

The [retained-edge continuation](COMPONENT_DN_RETAINED_EDGE.md) uses this
sweep to prove the full xs-to-st source transfer with arbitrary exterior
whenever f covers, with no cover assumption on r. It also handles the case
where r covers and a selected t-to-z path makes f redundant.

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

## Eliminating the DN deletion residual

2026-09-29. Retain the direct-split notation at the start of this note.
For every nonzero delta(Q), f is redundant in Q+e+f+q. The deletion
residual H(Q+e+q) can always be replaced by actual R states, with at most
one additional diamond:

    H(Q+e+q)=R11(Q)                                   (D1)

if x reaches z in Q. Otherwise choose the first edge alpha=wt on any
selected w-to-z bypass; put beta=xt. Then

    H(Q+e+q)=R00(sigma Q)+R11(Q-alpha+beta)
                                  -R00(sigma Q+alpha). (D2)

These are valuation identities for both K and E with arbitrary exterior.
In the second case x<t<z, beta is absent, and Q contains the entire
selected t-to-z suffix. The proof is the
[NN one-diamond elimination](COMPONENT_NN_REDISTRIBUTION.md#eliminating-every-unmatched-term-into-the-actual-rhs),
carrying e along in its three intermediate terms. In the two q-absent
terms, the swap sends e to the required e'. In the middle term e' is
redundant through e,q and can be inserted. In (D1), both e' and r are
redundant. Thus every output has both required strict edges e',r.

This removes the auxiliary H diagram from the general state-level split.
It does not assert that the new coefficient function is already constant
on target components. In particular, full output states can have more
selected edges than the residual. We use the unweighted induction K=E;
we do not infer polynomial coefficients for a recurrence in native
normal-selection weights by dividing by that parameter.

## A direct RHS-only repair for the left four-state component

The component C_1 in the five-vertex left table has a short repair using
only the actual DN target. Write

    a=01, b=12, c=13, e=02, q=23, p=03, r=34.

The source still has strict 02,24, and

    C_1={02+24+c+B : B in {a,b,q,r}}.

The target has all edges of the complete graph on 0,1,2,3 together with
34; p,r are strict. In the following brackets p+r are always included.
The initial DN split gives exactly

    X(C_1)=[ab]+[bc]+[b]-[c]+[ec]+[qc].                (D3)

The eight-state component already checked above is

    D_8={ab,bc,ea,qa,eb,qb,ec,qc},

with the same implicit strict edges. Its missing terms in (D3) are

    X(D_8)-X(C_1)=[ea]+[qa]+[eb]+[qb]-[b]+[c].         (D4)

Apply two diamonds retaining p, exchanging e,q, with backgrounds a and b:

    [ea]+[qa]=[a]+[eqa],
    [eb]+[qb]=[b]+[eqb].

Next use the p-diamond exchanging a,c and the e-diamond exchanging a,b
with q retained as background:

    [a]+[c]=[empty]+[ac],
    [eqa]+[eqb]=[eq]+[eqab].

Finally [ac]=[eq] by swapping vertices 1,2, and [eqab]=[abq] by deleting
redundant e. The swap fixes the strict edges and has one nonsink endpoint,
so it preserves both valuations. We obtain

    X(C_1)=X(D_8)-X(T_3)-2 X(T_4)-X(T_5),             (D5)
    T_3={p+r},   T_4={p+r+e+q},   T_5={p+r+a+b+q}.

All four outputs are whole components of the actual smaller target. The
three T's are isolated: at T_3 every possible exchange has both shorts
absent; at T_4 the long p is redundant and the shorts under e are both
absent; at T_5 every nonadjacent selected edge is redundant. The previous
D_8 check proves connectivity and absence of exits for its eight states.
Thus (D5) is a complete component recurrence, with no source additions or
assumed expansion for another source component.

For orientation, the T valuations are respectively e_(3,1,1), e_(4,1)
and e_5, since their reachability relations are a chain and isolated
vertices. We use the diagram equalities above to prove (D5), not a
comparison of elementary profiles. The target remains smaller in the
established first-drop order.

Related Rust: the `--rhs-only-audit --permuted-closures` check verifies
each of the four displayed diamonds, the swap and redundant deletion,
actual completeness of D_8,T_3,T_4,T_5, and the final equality separately
for exact K and E. It also verifies integral RHS-only collection for all
fourteen source components here, all fifteen in the minimal right-hand
picture, and all twenty-six in the fixed crossing six-vertex picture.
The full six-diagram table and receipt location are in the NN continuation.
The general simultaneous boundary repair for NN and DN remains unfinished.

Every map in (D3)--(D5) fixes vertices 0,4, and the only swap is internal.
The [endpoint-attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit)
therefore extends this same four-term component recurrence to arbitrary
components attached at these two ends. Its product-component and marked
HRV arguments apply without assuming expansions for the attached pieces.

## Prepared DN swaps and sector components

2026-09-29 continuation. We retain u<w<x=w+1<z, e=uw, e'=ux,
q=wx and r=xz in the actual DN target R. Its strict edges are e',r
and the unchanged common stricts. Define the double-bypass condition

    q is absent, and w and x both reach z in A-r.       (P1)

The adjacent swap sigma=(w x) fixes the common strict set and interchanges
e,e'. Away from q,r the natural edges of R are invariant under sigma.
The proofs below retain and relabel the entire exterior selection.

### The channel with e selected

Let S_1 contain the states satisfying (P1) with e selected. Then

    Phi_1(A)=sigma(A-r)+r                               (P2)

is an involution of S_1 preserving K,E and its induced actual flip graph.
The proof is the [prepared NN swap proof](COMPONENT_NN_REDISTRIBUTION.md#prepared-adjacent-swaps-and-their-component-boundaries),
with one decoration check. Both e,e' are selected, so their interchange
retains the strict e'. In the target the only natural edge properly
containing e is the new e'; a flip exchanging e must therefore exchange
it with q. An internal S_1 flip preserves absent q, so cannot exchange
e or e'. A flip retaining one of them is allowed to become a flip
retaining the other: retained long edges need not be strict. All other
strict edges remain fixed. These observations prove both directions of
the flip correspondence without an extra cover assumption on e or e'.

### The channel which inserts a redundant strict edge

Let S_0 contain the states satisfying (P1) such that e is absent and
u reaches w. Let T_1 contain the states satisfying (P1) such that e is
selected and e' is redundant. We claim that

    Phi_0(A)=sigma(A-r)+e'+r,
    Psi(B)=sigma(B-e'-r)+r                              (P3)

are inverse valuation-preserving isomorphisms between their induced flip
graphs. Phi_0 adds one selected edge in total.

**Proof of the state correspondence.** At A in S_0 the selected e'
is sent to e. The edge e' is missing from sigma(A-r), since A omits e.
The u-to-w path in A cannot use e', whose head is x>w, or r, whose
head is z. After the swap it becomes a u-to-x path. Thus adding e' in
(P3) is redundant. The two z-bypasses exchange, so r can also be
reinserted redundantly. The image belongs to T_1.

Conversely, take B in T_1. Delete redundant e',r. A u-to-x bypass of
e' cannot use e: using e would require a subsequent w-to-x path, which
is impossible with q absent and x=w+1. Nor can it use r. Its swap is
therefore a u-to-w path in Psi(B), which omits e. The selected e in B
becomes the required e', and the z-bypasses again justify insertion of r.
Thus Psi(B) belongs to S_0. Inspecting the selected sets in (P3) proves
that the two maps are inverse, not just inverse on reachability posets.
Each operation preserves K,E, as in the NN proof.

**Proof of flip transport.** A flip with both endpoints in either domain
preserves absent q, so its triangle cannot contain both w,x. On S_0,
it cannot exchange absent e or strict e'. On T_1 it cannot exchange e
without selecting q, and cannot retain redundant e'. Removing the stated
redundant edges changes no other cover. After the swap, a flip retaining
e' in S_0 becomes one retaining e in T_1; the inverse has the reverse
correspondence. The other triangles preserve their vertex order and
strict/normal status. Reinserting the redundant edges changes no tested
cover. This gives actual flips in both directions and proves the induced
graph isomorphism.

For example, in the six-vertex target with strict 03,14,35, the map sends

    A={01,03,12,14,24,34,35,45}
    to B={01,02,03,13,14,24,34,35,45}.                 (P4)

The 0-to-2 path in A is 01,12. Delete 35, swap 2,3, then insert 03
through 01,13 and restore 35 through 34,45. This is a prepared adjacent
swap, even though its two endpoint states have different edge counts.

### Corrections on complete induced components

For a complete component P of either induced domain, subtract the sum
on its image from the sum on P. This is a zero relation for both K and
E, and both sets are complete in their respective induced graphs.
A correction of this form preserves every internal coefficient comparison.
It can change a boundary comparison only when q is inserted or a required
reachability is lost. For S_1 these are the two z-bypasses; for S_0 we
also require the u-to-w path; for T_1 we also require the bypass of e'.
The status of e cannot change along a q-preserving flip. Thus the extra
boundaries in the second channel are precisely exposures of the incoming
corner in its two presentations.

This proves a uniform way to group prepared-swap corrections while
controlling which comparisons they can affect. The sectors are generally
not closed in the full target flip graph. We still have to cancel their
exits, together with the diamond corrections, before claiming the general
NN/DN whole-component recurrence.

Related Rust: `dn_joint_span --prepared-sectors` checks these maps and
both directions of internal flip transport. The crossing six-vertex
fixture has eight S_1 states with eight directed internal flips, and two
S_0 states. Its seven-vertex extension with additional strict 46 has
sixteen S_1 states with sixteen directed internal flips, and four S_0
states. The latter has genuine q-preserving exposure exits. All state
valuations and the domain/image equalities are exact. The separate
`--packet-corrections` run uses complete induced-component differences,
not arbitrary individual relabelings, in the six-diagram collection audit.
Receipts are in `prepared-swaps-20260929/` under the external project request
directory. No maintained Rust source, Lean build or extra worker is involved.

An additional eight-vertex fixture attaches a triangle at vertex 5, with
strict 57. It has thirty-two S_1 states and eight S_0 states. Both channels
have nontrivial internal flips, so their graph-isomorphism check is not
vacuous. This uses the same source/target maps, with the added attachment
retained in every state.

## Boundary descent for both prepared DN channels

2026-09-29. The [NN boundary identities](COMPONENT_NN_REDISTRIBUTION.md#descending-the-prepared-swap-boundary-identities)
also track the exits of both DN channels above. We give the decoration and
edge-count details, including the exceptional strict-long case.

Extend Phi_1 to every q-absent target state selecting e. Extend Phi_0
to every q-absent target state omitting e, using the same set formulas
(P2),(P3), whether or not the required bypasses hold. These formulas still
produce valid target states. Phi_1 preserves the edge count; Phi_0 adds
one edge. Equality of valuations is asserted only on their prepared domains.

For a q-preserving exit A->B, let s,t be the old and new shorts and put
E=A-s, F=A+t. Then, for either extended map Phi,

    Phi(A)<->Phi(B),
    [B]-[Phi(B)]=[E]-[Phi(E)].                        (B5)

For Phi_1 the NN argument applies with the two selected edges e,e'
interchanged. A q-preserving flip cannot exchange either of them. For
Phi_0, a flip retaining e' becomes one retaining e. The extra e' inserted
by Phi_0 is a maximal natural corner. Even when it ceases to be redundant
at Phi_0(B), its insertion cannot affect the other tested covers. The same
holds for r. No exchanged edge becomes a strict edge: e is absent in the
source and cannot change along a q-preserving flip.

The two paired diamonds therefore remain valid. The full state F contains
A, preserves e's status, and retains all the required paths, including
u-to-w in the Phi_0 channel. Hence [A]=[Phi(A)] and [F]=[Phi(F)]. Their
cancellation proves (B5). Each state of the right pair has one fewer
selected edge than its corresponding state on the left, including the
one-edge offset between the two Phi_0 channels.

For an exit inserting q, the two exchanged arms in the q-triangle are
both selected at A and interchanged by sigma. Their covers survive the
prepared map, so the same s->q exchange is actual at A'=Phi(A). Let B'
be its endpoint. The two diamonds give, with all exterior retained,

    [B]-[B']=[A-s]-[A'-s]+[A+q]-[A'+q].               (B6)

In the Phi_0 channel the triangle cannot be u,w,x: that exchange would
require the absent e to be selected. Thus both arms of its q-triangle
belong to the common exterior, as needed for this pairing.

If the retained long ell is normal, delete it from the two full terms
in (B6). This gives precisely (B2), including the strict increase of
reachability at unchanged edge count. The only possible strict ell is
e'=ux, in the Phi_1 channel. Its exchanged normal shorts are e,q. In
that case the full terms make e' redundant through e,q. Delete e' in
BOTH terms, interpreting them in the ordinary smaller diagram

    J=R-e', with r and all common strict edges retained strict.

Deletion is valid because e' is a natural corner, and no other edge of
the full terms is lost. The two empty terms stay in R. Thus even the
strict-long case yields a signed identity of states in smaller ordinary
diagrams, with the same coefficients for K,E. We do not keep a state
omitting e' while calling it a state of R.

With this interpretation, every resulting pair strictly decreases the
measure (B3): the empty pair loses one edge at each endpoint, while the
pruned full pair keeps the counts and strictly increases reachability.
This is a proved local descent for every boundary type of the two
prepared DN channels. Neither the R terms nor the J terms have yet been
shown to collect uniformly into whole components. In particular, deleting
a redundant strict edge in these individual full terms is not an appeal
to the stronger whole-component inactive-corner lemma.

Related Rust: `--boundary-identities` verifies the paired actual flips,
exact K/E identities, both count changes, and strict inclusion of the
reachability relations. When ell=e', it constructs J and checks that its
natural edge set is exactly R minus e', and that both pruned relations
are valid there. In the crossing six-vertex example the Phi_1 counts are
four bypass-loss, ten normal-long q-insertion and five strict-long
q-insertion boundaries; Phi_0 has one bypass-loss and three normal-long
boundaries. The attached eight-vertex fixture checks the same identities
with nontrivial exterior component flips. Frozen sources, commands and
receipts: `prepared-boundaries-20260929/` under the external request folder.
No Lean build, maintained Rust edit, extra worker or independent review
is used. The remaining global closure obligation is stated after (B3).


## Following the two DN swaps through further flips

2026-09-29 continuation. We use the same diagram argument as
[the NN continuation](COMPONENT_NN_REDISTRIBUTION.md#following-the-swap-through-a-further-flip).
No change of basis or component-expansion theorem enters it.

The formula Phi_1(A)=sigma(A-r)+r works on every q-absent state with
e selected. It transports actual flips in both directions once we omit
flips retaining r. The formula Phi_0(A)=sigma(A-r)+e'+r works on every
q-absent state with e absent, with inverse sigma(B-e'-r)+r. Here we
omit r-retaining flips on both sides and e'-retaining flips on the image
side. A domain flip retaining e' becomes one retaining e and is allowed.
The extra inserted e' is a maximal natural corner, so it cannot alter
the other cover tests. A q-preserving flip cannot exchange e. These
facts prove the correspondence even when a bypass has disappeared.
They do not imply equality of the individual diagram values.

For every matched flip, the two diamonds give exactly (C1). If a retained
long is strict on one side, interpret its pruned full term in the smaller
diagram deleting that corner on that side. The other strict edges stay
selected. This includes the case where e' swaps to normal e. The two
endpoints may therefore belong to different smaller decorated diagrams.

Starting from a prepared matched pair, we can now follow every flip
inside either of these restricted graphs, using (C1) at each step.
Eliminating leaves of a spanning tree gives the same integral identity
for complete pieces as in NN. The one-edge difference between A and
Phi_0(A) is harmless: each empty term loses an edge on its own side.

What remains is to close the excluded flips and assemble all signed
terms from the original source component into whole components. The
restricted pieces themselves are not whole RHS components. We do not
replace this last check by a general statement about arbitrary pairs.

Related Rust: `--extended-packets` verifies both flip correspondences
and the complete-piece identities, including the attached eight-vertex
example where both DN channels have nontrivial internal flips. Frozen
sources and receipts: `coupled-coefficients-20260929/` under the external
request folder. The general NN/DN collection remains unfinished.

# Completing a DN image by adding deletable components

2026-09-28. We give a six-vertex component recurrence obtained by adding
two whole source components, applying the direct DN identity, and subtracting
the added components in smaller diagrams. The proof uses the same coefficients
for the strict coloring sum K and the HRV elementary expression E.
The general source-addition construction remains open.

We use [direct DN transport](COMPONENT_DN_DIRECT_OVERLAPS.md) and the
inactive-corner deletion lemma in
[flip-component induction](FLIP_COMPONENT_INDUCTION.md). If a natural corner
is redundant throughout a complete component, deleting it gives a complete
component in the corner-deletion diagram, with both valuations unchanged.
An absent unmarked natural corner can also be deleted. Redundancy at just
one orientation does not suffice.

## The six-vertex example

Let L have area sequence (0,1,2,2,3,3). Its strict edges and normal edges are

    e=02, g=14, f=25;
    a=01, b=12, c=13, q=23, d=24, s=34, r=35, t=45.

We apply DN at (u,w,x,z)=(0,2,3,5). The target R has area
(0,1,2,3,3,2), strict edges 03,14,35, and normal edges
01,02,12,13,23,24,34,45. The common deletion diagram H has area
(0,1,2,2,3,2), with only 14 strict.

Let F_L be all source orientations with nine selected edges, including the
three strict edges. We specify an orientation by its pair of omitted normal
edges. Thus F_L has 28 members. Three of these are isolated:

    S_cd omits {c,d},   S_cr omits {c,r},   S_dr omits {d,r}.

Indeed, each selects every adjacent edge. Every selected nonadjacent edge
is then redundant, so none can retain a flip.

Two further complete components are

    I_3 = {01,02,12,14,24,25,35} + choose two of {23,34,45},
    I_4 = {02,13,14,24,25,45} + choose three of {01,12,23,34}.

Here the notation denotes the set of all indicated edge selections.
In terms of omitted pairs, I_3 consists of {c,q},{c,s},{c,t}, and I_4
consists of {r,a},{r,b},{r,q},{r,s}.

The component I_3 is a three-state path: retain 24 to exchange 23,34,
and retain 35 to exchange 34,45. Corner 02 is redundant through 01,12;
14 through 12,24; and 25 through 23,35 or 24,45. These corners cannot
retain a flip. All other potential flips either exchange two present
edges or require the absent 13. This proves completeness.

In I_4, corner 25 is redundant through 24,45. Corner 14 is redundant
through 12,24 when 12 is selected, and otherwise through 13,34.
The only remaining flips exchange adjacent unequal bits in
(01,12,23,34), retaining respectively 02,13,24. Thus I_4 is a complete
four-state path. We may delete 02 from I_3 and 14 from I_4, obtaining
whole components in areas (0,1,1,2,3,3) and (0,1,2,2,2,3), respectively.

The remaining 18 orientations form one complete component C. To check
connectedness without listing its orientations, first take the ten omitted
pairs from {a,b,q,s,t}. Adjacent exchanges along this five-letter list,
retaining 02,13,24,35, connect these ten pairs. The remaining pairs join
them as follows; arrows denote actual flips of omitted pairs:

| Additional pairs | A connecting flip | Retained edge |
| --- | --- | --- |
| {a,c}, {b,c} | {b,c} ↔ {b,s} | 14 |
| {a,d}, {b,d}, {q,d} | {q,d} ↔ {q,t} | 25 |
| {s,d}, {t,d} | {s,d} ↔ {s,b} | 14 |
| {r,t} | {r,t} ↔ {q,t} | 25 |

Within each row, the same adjacent exchanges connect its listed pairs.
For each connecting flip, the other omitted edge breaks the alternative
path that could make its retained edge redundant. The selected short
also covers. This verifies the displayed flips. Since I_3, I_4 and the
three singletons are complete and account for every other member of F_L,
the connected remainder C is complete as well.

## Matching the terms

Let F_R be the target orientations with nine selected edges. Let

    T  = {01,02,03,12,14,23,34,35,45},
    H1 = {01,02,12,13,14,23,34,45},
    H2 = {01,02,12,14,23,24,34,45}.

The first is an isolated orientation of R and the other two are isolated
orientations of H: each selects all adjacent edges of its diagram.

The direct DN image of F_L is exactly F_R. To see this, let m count the
selected exterior normals among {a,b,c,d,s,t}. For the indicator h of F_L,

    h00 = [m=6],   h10=h01 = [m=5],   h11 = [m=4].

The adjacent vertex exchange sigma preserves m. Substitution in the direct
formula therefore gives the indicator of F_R, with zero deletion term.
The three isolated source orientations have the following individual images:

    S_cd -> T,   S_cr -> H2,   S_dr -> H1.

The first uses the full DN identification. Each of the other two lies in
the 10 sector, so its only contribution is the single deletion term.
By linearity, for both X=K and X=E,

    X_L(C)+X_L(I_3)+X_L(I_4)
      = X_R(F_R\{T})-X_H(H1)-X_H(H2).

Flips preserve the number of selected edges. Consequently F_R is a union
of complete components; removing its isolated member T preserves this
property. Deleting the redundant corners in I_3 and I_4 now gives

    X_L(C)
      = sum_{D a component in F_R\{T}} X_R(D)
        - X_H(H1) - X_H(H2)
        - X_{L-02}(I_3-02) - X_{L-14}(I_4-14).

This is the desired recurrence for the original component C. Every term
on the right is a whole component in a smaller diagram. Corner deletion
decreases doubled area; DN preserves doubled area and decreases the
secondary moment sum_j j a_j, as in
[the ordinary DN measure](DN_COMPONENT_COMPLETION.md).
The target union consists of components of sizes 18,4,3,1,1, but their
individual classification is unnecessary for the proof.

## The general question and exact checks

The example suggests the following sufficient construction. Given a
component C that cannot be deleted directly, add whole source components
I for which an absent or everywhere-redundant natural corner can be deleted.
Choose their coefficients so that the direct DN image is constant on every
complete component of R and H. Subtract each added I in its own smaller
corner-deletion diagram. This does not require the deletion term to vanish.

We have not proved that such additions always exist. The local comparisons
to be repaired are precisely the two five-vertex pictures in the direct
transport note. The task is to construct the additions from those
comparisons and prove that they close every affected boundary. We make no
uniqueness assumption about components active at all corners.

An exact check solves only these constancy equations, with the coefficient
of C fixed to one and those of other nondeletable components fixed to zero.
It does not use zero-relation generators in R or H, or assume any component
HRV formula. In all the following selected diagrams, a solution exists for
every component that cannot be deleted directly:

| Source area | Strict edges | All components | Components tested |
| --- | --- | ---: | ---: |
| 01123 | 01,14 | 15 | 6 |
| 01222 | 02,24 | 14 | 4 |
| 011234 | 01,15 | 116 | 23 |
| 012233 | 02,14,25 | 26 | 11 |
| 0122332 | 02,14,25,46 | 28 | 13 |
| 0112343 | 01,15,36 | 177 | 30 |
| 0123323 | 03,36 | 436 | 28 |

All 115 solutions add components with coefficient one. Each used deletion
is checked to give a complete component, all output coefficients are checked
for constancy on whole components, and the resulting K and E identities are
checked separately and exactly. These are selected diagrams, not an
exhaustive seven-vertex result or a proof with arbitrary exterior.

We also form the full homogeneous constancy equations, with one variable
for every source component. In these seven diagrams their reduced rows
are all equalities between two source-component coefficients. The ranks,
in table order, are 1,2,19,3,3,24,108. Thus the observed completion amounts
to taking unions of components. We have not proved this description of
the equations in general. One general simplification is already proved:
[every target 00 comparison follows its 10 comparison](COMPONENT_DN_DIRECT_OVERLAPS.md#the-00-comparisons-follow-the-10-comparisons).
The remaining q-changing comparisons still need a general matching rule.

For such a comparison R00(V) ↔ R01(P), its equation is

    [h00(sigma V)-h01(P)] + [h01(sigma V)-h01(V)] = 0.

The two brackets involve consecutive source edge-count layers. They cannot
simply be set to zero separately. In particular, the second bracket need
not vanish after imposing all H comparisons and all target comparisons
that avoid 00. An exact counterexample occurs in area 011234, strict01,15.
Take h to be the indicator of the union of the complete components with
seeds

    {01,12,13,15,23,24,25,34},
    {01,12,13,15,23,24,34,35}.

Their sizes are nine and four. This h satisfies all the stated comparisons,
but for V={13,14,23,34,35} we have h01(sigma V)=1 and h01(V)=0.
The target R00(V) has the actual flip retaining 13 and exchanging 23,12.
The diagnostic checks every imposed equation and both displayed values.
Thus the remaining comparisons must be used together; the simpler
separate-bracket implication is false even in this six-vertex diagram.

Related Rust: the external `hrv-bridge/src/bin/dn_joint_span.rs` consumer uses
`nn_component_transport::{components, valuations}` and the shared
`sym_poly_core::sparse_linear_algebra::sparse_rref`. Its source-addition mode
solves the explicit coefficient equations. Frozen source, commands, logs,
independent audit and checksums are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-left-exterior/`.
No Lean source or manuscript is changed by this note.

## The unmarked upper corner forces source additions

2026-09-29 continuation. We isolate a boundary which cannot be settled by
extending the conditional source-path lemmas. This occurs in an actual
first-drop DD step, so it remains part of the restricted completion target
in the main outline. The required repair is a coefficient correction.

Let D have strict corners e=uw, f=wz and h=(u+1)x, where x=w+1 and
u+1<w. Unmark h to obtain the DN intermediate N. Put a=u(u+1).
The status of h is invariant on every complete N-component: it is still
a natural corner. The h-selected components are exactly those of D;
the h-absent components are whole components in N-h=D-h, a smaller
natural diagram. These are the existing corner identifications, with
arbitrary exterior and no restriction on selected cycle rank.

In the DN target, e'=ux properly contains h. It can retain an actual
flip a<->h. In the R10 sector, the direct coefficients at that comparison
are the source multiplicities at

    A=L01(Q+a),             B=L01(Q+h).              (8)

The two source states have opposite h-status and therefore can NEVER
belong to the same N-component. Thus, if B belongs to the chosen original
component C, its indicator gives coefficients 0 and 1 at this actual target
comparison. No source path can make them equal. The cover hypotheses for
the target comparison are still required; we do not assert that every Q
supports the comparison.

### A first-drop example and its complete repair

Take D with area 01222 and all three corners 02,13,24 strict. Its first
strict area drop is after vertex 4, with the DD contact (u,w,x,z)=(0,2,3,4).
Unmark h=13. In N the four states

    C={02,13,24}+choose one of {01,12,23,34}

form one complete component. Each flip exchanges adjacent unequal choices
along this four-edge list, retaining 02,13 or 24. The h-absent component

    I={02,24}+choose one of {01,12}+choose one of {23,34}

is a complete square: the two independent exchanges retain 02 and 24.
Both descriptions include all possible source flips, since every natural
long is one of these three length-two corners. The h-status distinguishes
the two components.

In particular A={01,02,24,34} belongs to I, whereas
B={02,13,24,34} belongs to C. The target, of area 01231 with 03,34 strict,
has the actual flip

    {01,02,03,34} <-> {02,03,13,34}, retaining 03.   (9)

The exchanged shorts 01,13 and the retained 03 have the required covers.
Its direct t10 coefficients for the indicator of C are 0 and 1. This
explicitly refutes unrestricted left source-connectivity for the DD
intermediate, including when the original component selects the unmarked
upper corner. Selecting that corner does not remove (9) from the target.

The obstruction is not confined to forest components. Add 12 to both A
and B and to the two target states in (9). The target flip is still actual.
The selected-h source component is now the six-state connected unicyclic
component C_2 from the minimal left calculation, whereas its h-absent
partner is the two-state I_21. Its representative
{02,12,13,24,34} is acyclic after reversing all three strict corners:
3,1,4,2,0 is a topological order for the resulting mixed graph. Thus the
usual disconnected, forest and mixed-cycle reductions do not exclude this
counterexample to the source-path assertion.

Adding I with coefficient one repairs this boundary. Here it also completes
the entire DN image, as proved in the
[five-vertex left construction](COMPONENT_DN_JOINT_REPAIRS.md#a-complete-component-recurrence-for-the-left-hand-diagram):

    X_D(C)=X_R(D8)-X_(D-h)(I),          X=K,E.         (10)

The eight-state D8 is the whole target component listed there. Its complete
reassembly is essential to (10); the single comparison (9) alone would
not prove that recurrence. Both output diagrams decrease the ordinary
induction order. This is a worked instance of the notebook's component
completion by adding and then subtracting a deletable component.

### Exact equations for this boundary, with arbitrary exterior

Suppose we fix integer multiplicities m(C) on the h-selected source
components. For each h-absent component I, let N(I) be the set of
h-selected components containing a state B paired with a state A in I
as in (8), for an ACTUAL target R10 flip a<->h.

**Proposition.** We can assign multiplicities m(I) to the h-absent components
so that the unmodified direct DN coefficients agree on every target flip
retaining e' and exchanging a,h if and only if m(C) is constant on N(I)
for each I. If N(I) is nonempty, m(I) is forced to be that common value;
if N(I) is empty, we may set m(I)=0.

**Proof.** At each R10 comparison, direct transport gives exactly the
equation m(I)=m(C), by (8). Necessity follows. Conversely, the proposed
assignment satisfies all these equations, hence every R10 comparison
of this type. The
[sector reduction](COMPONENT_DN_DIRECT_OVERLAPS.md#all-left-retained-e-prime-comparisons-reduce-to-the-10-sector)
then supplies the 00 and 01 comparisons; the 11 sector has no actual
flip retaining e'. This proves sufficiency for this boundary subsystem.
Every added I is a whole component of D-h, independently of the assignment,
so it has an available smaller-diagram interpretation for both valuations.

For the indicator of one C, this says that every h-absent I meeting C is
forced to have coefficient one. Such an assignment can leave every other
h-selected component at zero exactly when no such I also meets a different
h-selected component. We have not proved this compatibility in general.
Nor does the proposition settle the other left vertices, q-changing flips,
or the deletion-diagram coefficients. Those may require further source
additions or joint diamond corrections. If output coefficients themselves
are changed by zero-valuation identities, the displayed equalities need
not remain the full repair equations; the necessity assertion is explicitly
for source additions followed by the unmodified direct split.

The proposition therefore identifies a compulsory first part of a
source-addition construction, rather than asserting that the complete
construction always exists. It also prevents a false proof target:
unrestricted source connectivity cannot replace coefficient reassembly.

### Verification

Related Rust: the existing external `first_join_tree_lifts.rs`, option
`--dd-boundary-check`, checks the two four-state source components, their
opposite h-status, the target comparison and its 00 version, and all
R01-to-R10 lifts in this fixed target. It also checks the six-/two-state
unicyclic comparison and the displayed mixed-acyclic witness. The established `dn_joint_span`
binary, `--left-repair --skip-span`, independently replays the complete
fourteen-component minimal left calculation, with whole target/deletion
components and exact K/E identities. These checks support (9)--(10);
the arbitrary-exterior proposition is proved by the coefficient equations.
No new general compatibility or independent review is claimed.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/common-preparation-20260929/`.

## Completing one selected-edge layer of the direct DN image

2026-09-29 continuation. We now prove an exact description of the
source additions for one fixed total number of selected edges. We use
the existing direct DN split, its flip lifts and whole source components.
The result determines the smallest union whose direct image is a sum of
whole output components. It does not yet prove that all added components
have independent reductions, which is what would isolate the original C.

The fixed-edge-count restriction is substantive. We do not split the two
brackets of the earlier arbitrary-degree counterexample independently.
The theorem below concerns a coefficient function supported on one layer.

### The two output sizes

Fix k and let m be an integer function on source components with k selected
edges, extended by zero to all other source states. Write m_ij(Q) for its
value on Lij(Q). The background Q includes the common strict edges, so

    |Lij(Q)|=|Rij(Q)|=|Q|+2+i+j.

For a target state T define its source lift by

    phi(R00(Q))=L00(sigma Q),
    phi(R10(Q))=phi(R01(Q))=L01(Q),
    phi(R11(Q))=L11(Q).

This lift preserves the total selected-edge count. The direct transport
coefficients separate as follows:

| Output size and sector | Coefficient |
| --- | --- |
| R, size k, any sector T | m(phi(T)) |
| R00(Q), size k-1 | m_01(sigma Q)-m_01(Q) |
| R, size k-1, other sectors | 0 |
| H10(Q)=Q+e+q, size k-1 | m_10(Q)-m_01(Q) |
| H, all other states | 0 |

All other R sizes have coefficient zero. This table is a direct
substitution in the proved formula; it does not assume any component
reassembly. In particular, m_00(sigma Q) and m_01(sigma Q) cannot both
contribute at the same Q when m is supported at k.

### Three kinds of required equalities

On the set of complete source components with k selected edges, impose
the following pairwise equalities. Brackets mean actual source components.
Every flip mentioned is required to be actual in its full output relation.

1. For every R flip T<->T' between states of size k, equate
   [phi(T)] and [phi(T')].
2. For every R00(Q) of size k-1 with an actual flip leaving the 00 sector,
   equate [L01(sigma Q)] and [L01(Q)].
3. For every H10(Q) of size k-1 with an actual flip removing q,
   equate [L10(Q)] and [L01(Q)].

Let U_k(C) be the class of C generated by these equalities. Equivalently,
join each displayed pair by an undirected edge and take the connected
class of C. This is the same component-closure construction used by the
existing external diagnostic; no assertion of actual source connectivity
is implicit in an imposed equality.

**Homogeneous completion theorem.** The direct DN coefficients of m are
constant on every complete R and H component if and only if m is constant
on every class U_k(C).

**Proof of necessity.** At size k, the first row of the table makes every
R comparison exactly the equality in item 1. At an exit from R00 in size
k-1, the coefficient at the other endpoint is zero, so item 2 is forced.
The statuses of e and r are fixed in H because both are natural corners.
Thus an H flip removing q leaves the supported sector, whose other
endpoint has coefficient zero. Its comparison forces item 3. Constancy
on output components therefore implies every generating equality.

**Proof of sufficiency.** Item 1 handles all R comparisons at size k.
At size k-1, the only possibly nonzero R coefficients are in 00. Item 2
handles every exit from that sector. For an actual comparison
R00(Q)<->R00(P) within it, two already-proved lifts apply:

- The bottom swap gives an actual source L00 comparison on sigma Q,
  sigma P; adding r gives an actual L01 comparison there. Consequently
  m_01(sigma Q)=m_01(sigma P) for any source-component function m.
- Adding e gives an actual R10 comparison on Q,P, now of size k.
  Item 1 therefore gives m_01(Q)=m_01(P).

The difference in the second row of the table is constant. These lifts
also apply to a 00 comparison retaining e', as proved in the
[opposite-defect lemma](COMPONENT_DN_DIRECT_OVERLAPS.md#the-00-comparisons-follow-the-10-comparisons).
Comparisons outside 00 have two zero coefficients. This settles every R
comparison at size k-1 and hence every R component.

For H, the previously proved q-preserving lift makes
m_10(Q)-m_01(Q) constant on all comparisons staying in the supported
sector. Every flip leaving it must remove q, since e,r are corners,
and item 3 makes its coefficient zero. Every other comparison has two
zero coefficients. Thus all H components have constant coefficients as
well. There is no missing exterior comparison, because each output flip
belongs to one of the cases just considered. This proves sufficiency.

### The smallest union and its complete output

Take m to be the indicator of U_k(C). The theorem and the direct transport
identity give, simultaneously for X=K,E,

    sum_(I in U_k(C)) X_N(I)
       = sum_(D an R-component) a_D X_R(D)
         + sum_(B an H-component) b_B X_H(B).        (11)

All displayed output terms are whole components. Each a_D,b_B belongs
to {-1,0,1}: the table has either an indicator or a difference of two
indicators, and each component has a constant value. The nonzero R terms
of size k have coefficient +1. Negative coefficients may occur in size
k-1 and cause no problem for an induction comparing K with E.

Moreover, U_k(C) is the smallest union of k-edge source components
containing C whose unmodified direct image has complete output components.
Indeed, the indicator of any such union satisfies all the generating
equalities, so it is one on the entire class of C. The same argument
shows that any integer-valued completion with m(C)=1 must have m(I)=1
for every I in U_k(C); negative source coefficients cannot cancel that
requirement within this one layer.

Suppose every I in U_k(C) other than C has an independently proved
same-coefficient reduction into whole smaller components. Subtract those
reductions from (11). This gives precisely the individual recurrence
required for C, with the same coefficients for K and E. The R diagram
has the forward-DN decrease in area moment; H has one fewer natural edge.
Their whole components, and the independently reduced source additions,
are therefore available to the ordinary induction.

In particular, if the permitted additions are a specified collection A
of independently reduced source components, then a completion supported
at k, using C and components of A only, exists exactly when

    U_k(C) minus {C} is contained in A.               (12)

Necessity follows from the forced value one on the class, and sufficiency
uses its indicator. This is an exact criterion for the unmodified direct
split with additions in one selected-edge layer. It is not a necessary
criterion for all diagram-bijection proofs: corrections by output diamonds,
other recurrences or additions in different layers remain possible.

### Relation to the local repairs and the remaining proof

The arbitrary-exterior source paths already proved turn the corresponding
item-1 edges into loops on a source component. The DD upper-corner boundary
supplies genuine item-1 edges to absent-corner components, which are
independently smaller. Items 2 and 3 record the remaining target-zero-sector
and deletion boundaries. The theorem includes all three families together;
repairing only the left retained-e' comparisons is not enough.

The remaining sufficient statement for this route is that, for the chosen
first-drop recurrence and an unreduced original C, every other member of
U_k(C) is independently reducible. We have not proved it. In particular,
it is not enough that each first neighbor added at one DD boundary is
deletable: subsequent equalities can reach further source components.
Nor do we assume uniqueness of a component active at all strict corners.
If (12) fails for the chosen collection of known reductions, the other
allowed joint corrections must still be considered.

This theorem proves the pairwise description for a homogeneous source
layer. It does not prove the earlier observed pairwise reduced-row form
for the full system permitting simultaneous coefficients in different
layers. The earlier counterexample to separating its brackets remains
valid and is not bypassed by the degree restriction.

### Exact checks

Related Rust: the established external `dn_joint_span` binary, with
`--component-closure --source-additions=active --all-corner-deletions
--skip-span`, constructs the homogeneous pair equations directly from
actual output flips. No new computation implementation was needed.
For fixed area 012233 it checks 736 comparisons, obtains three pair
edges and 23 classes among 26 source components, and gives a valid
completion for all eleven components not directly corner-deletable.
This includes the class consisting of the 18-state C and its three-/
four-state deletable additions in the earlier example. The smaller fixed
area 01222 checks the DD boundary example as well.

For each reported completion the diagnostic checks the original coefficient
equations, complete output components, complete corner-deletion images and
the exact K/E identity. These are fixed small diagrams, not a general proof
of (12). The theorem above is the arbitrary-exterior proof of closure and
minimality; general reducibility of the added components remains open.
No Lean/Lake build, new worker, consultant or maintained Rust change was used.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/homogeneous-dn-closure-20260929/`.

## Isolating one selected-corner sector by a full layer

2026-09-29, after the endpoint-attachment checkpoint `df1ea28`. We give
a sufficient source-addition criterion which avoids repairing individual
output flips. It supplies whole-component recurrences for every saturated
square of a path, with arbitrarily many vertices. This family already has
an expansion by the separate aggregate argument in the
[active-corner note](COMPONENT_ACTIVE_CORNERS.md#a-uniform-case-all-maximal-intervals-have-length-two).
The new conclusion here is its explicit diagram recurrence, with independent
reductions of every extra source component. We do not use that expansion
or the general word-functional theorem in this construction.

For a decorated diagram D, let F_m(D) be the set of all its selected
states with exactly m selected edges, including the strict edges. We
use X(F_m(D)) for the sum over this set. Since flips preserve m, this is
always a union of complete components; a layer can be empty.

### The full DN layer has no boundary defect

Let N be any eligible forward DN source, with target R and common
deletion diagram H as above. Then, for both X=K,E,

    X(F_m(N)) = X(F_m(R)).                              (13)

This follows directly from the diagram identities. For the indicator of
F_m(N), and b=|Q|, we have

    h00(Q)=[b+2=m],  h10(Q)=h01(Q)=[b+3=m],
    h11(Q)=[b+4=m].

The adjacent interchange sigma preserves |Q|. Thus delta=0, the two
h01 terms in t00 cancel, and the four target coefficients are exactly
the indicators of |Rij(Q)|=m. In particular (13) is already an identity
between unions of whole components, with no remaining H term.

**Selected-corner criterion.** Suppose N has an unmarked natural corner
g, and exactly one complete component C in F_m(N) selects g. Then

    X_N(C) = X(F_m(R)) - X(F_m(N-g)),     X=K,E.        (14)

Every term on the right is a union of whole components in strictly
smaller diagrams for the forward DN order.

Indeed, g cannot be exchanged as a short edge, so its status is constant
on each source component. By the uniqueness hypothesis, all other members
of F_m(N) omit g. The identity map identifies that entire absent-g sector
with F_m(N-g), component by component. An absent retained edge cannot
support an actual flip, so deleting it neither removes nor adds a flip;
selected relations and cover tests are unchanged. Subtract this sector
from (13). The R diagram decreases the area moment at fixed area, while
N-g decreases area. These are independent reductions of every added
source component, not merely a zero valuation for their combined defect.

The same proof allows a set of unmarked natural corners: if C is the
unique component of F_m(N) selecting all of them, every other component
omits at least one such corner and deletes there. We subtract each whole
component only once, choosing one of its absent corners. This variant
does not require an inclusion-exclusion identity or overlapping copies.

The uniqueness hypothesis concerns a specified layer and selected-corner
sector. It is not a claim of uniqueness for arbitrary active components,
and it is not yet known at general first-drop contacts.

### A uniform square-of-a-path recurrence

Let n>=5, and let D_n have natural edges ij with 1<=j-i<=2, all
distance-two edges strict. Its area sequence is

    (0,1,2,...,2).

For 0<=k<=n-1, write C_(n,k) for the states selecting k of the n-1
adjacent edges, together with all n-2 strict edges. This is one complete
component. Its flips are exactly exchanges 10<->01 in the binary word
of adjacent-edge selections: each natural triangle consists of three
consecutive vertices, its adjacent selected short is a cover, and its
retained distance-two edge has no alternate path when exactly one short
is selected. These exchanges connect all words of weight k. This also
checks all possible flips and hence completeness.

The first area drop is at the last vertex. Its DD contact has

    u=n-5, w=n-3, x=n-2, z=n-1,
    e=(n-5,n-3), f=(n-3,n-1), g=(n-4,n-2).

Unmark g, obtaining the eligible DN source N_n. The g-selected sector
is the unchanged flip graph of D_n. Thus C_(n,k) is its unique g-selected
component with m=n-2+k total selected edges. The extra source components
all have g absent and delete independently to J_n=N_n-g.

Define R_n by replacing the natural edge f with e'=(n-5,n-2), marking
e' and r=(n-2,n-1) strict and retaining every other strict edge of N_n
except e,f. The old edge e becomes normal. In area coordinates, R_n
has the same rows as D_n except

    a_(n-2)=3,   a_(n-1)=1.

The deletion diagram J_n has a_(n-2)=1, with all other rows unchanged,
and its strict edges are the distance-two edges other than g. Applying
(14) gives the promised recurrence

    X_Dn(C_(n,k))
      = sum_(B a component of R_n; |B-state|=n-2+k) X_Rn(B)
        - sum_(I a component of J_n; |I-state|=n-2+k) X_Jn(I),
        X=K,E.                                          (15)

Here |B-state| means the number of selected edges of any state in B,
which is constant on B; it is not the number of states of B. All
coefficients are +1 or -1, all outputs are whole, and every output
diagram is smaller. Specifically A(R_n)=A(D_n), M(R_n)=M(D_n)-1,
and A(J_n)=A(D_n)-1. This proves the required push-through step for
every component of D_n, with no bound on n or cycle rank.

We can also describe the subtracted components explicitly. Omitting g
removes the exchange between the two adjacent-edge bits at positions
n-4 and n-3. The remaining flips permute a left word of length n-3
and a right word of length 2 independently. Thus the J_n layer splits
into components I_(i,j) with i+j=k+1, 0<=i<=n-3, 0<=j<=2, of sizes

    binomial(n-3,i) binomial(2,j).

These descriptions concern entire source additions; no member is
discarded because a corner happens to be redundant at that member.

For n>=6 the contact has crossing exterior edges, for example the strict
edge (n-6,n-4) enters the interior of the five displayed vertices.
Thus (15) is not simply the endpoint-attachment theorem applied to the
five-vertex table. It handles these particular crossing exteriors by
the full-layer construction. It does not handle arbitrary crossing
exteriors: there may then be several g-selected components at the same
selected-edge count, and (13) alone gives only their sum.

All operations used in (15) fix the outer vertices 0,n-1. By the
[endpoint-attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit),
the recurrence also extends to arbitrary complete components attached
at these outer vertices, with the same whole-component and measure claims.

### Verification and the remaining general step

The existing external consumer now has `--square-path-layers`. It reuses
the actual-flip component BFS and the maintained exact strict P-partition
and HRV APIs. For each of n=5,6,7, every k=0,...,n-1 passes (15):
eighteen fixed recurrences. Each source set is verified as a complete
component; every target is a union of actual complete components; every
deleted component lifts back to an entire g-absent source component.
The K and E identities are checked separately using exact rational
coefficients. Each diagram has at most 128 admissible states. The
uniform proof is the binary-word and full-layer argument, not an
extrapolation of these checks.

Frozen sources, build output and check output are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/square-path-layers-20260929/`.
No Lean/Lake build, maintained Rust edit, worker or consultant was used.
The whole-component recurrence for general NN/DN contacts remains open:
we still need to isolate a component when several unreduced components
survive in its selected-corner sector. Neither (14) nor (15) assumes
that uniqueness in general.

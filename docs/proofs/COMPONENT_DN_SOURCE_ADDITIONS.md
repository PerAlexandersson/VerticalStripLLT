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

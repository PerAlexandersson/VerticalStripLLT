# Flip-component induction: redistribution and component equations

Status: the primary proof route, following the author's component-through-
recurrences idea. The integer transport criterion below and the later corner
reductions are proved mathematical lemmas. Their required global recurrence
certificates remain to be constructed. No full component proof is claimed.
No Lean source or Overleaf manuscript is changed by this audit.

The current concrete continuation is
[ordinary DN component completion](DN_COMPONENT_COMPLETION.md): it proves
reconstruction for an explicitly generated union of source components and
isolates the remaining question of whether two unsolved components can be
joined. This note retains the general signed framework and its exact local
identities; the continuation does not duplicate them.

We read `LLT flip/main.tex`, especially the local diamonds (around 1704),
component target (around 1980), cut/transport/reassembly discussion
(2527–2595), relations (1')–(4'), signed transfer discussion (3007–3095),
and commented relation-(8') sketch (3387 onward). We also read
`EDITORIAL-AUDIT.md` and the repository component interface. `new-main.tex`
is a shorter partial rewrite, not a replacement for the detailed sketches.
The prior audit's finite computational claims are provenance, not new checks
or proofs performed in this continuation. Independent Astra and Terra reviews
were read-only and build-free.

## The desired induction

Write K_C for the sum of weak order enumerators of orientations in a complete
flip component C, and H_C for its sum of HRV complete-homogeneous monomials.
The strict/e version uses the existing Lean coefficient interface. We retain
that convention for future formalization; omega is not the central issue here.

We want to show that validity for all components of suitable smaller diagrams
implies validity for every component of the source. This is compatible with
redistributing individual coloring occurrences among orientations and among
components. A correspondence between whole orientation components need not
be the primitive operation.

There are two separate obligations:

1. Prove simultaneous local transport identities for K and H with exactly
   the same coefficients, including the actual exterior relations.
2. Prove that enough transported identities isolate each source component.

The aggregate circular theorem does not supply either obligation merely by
summing its orientations differently.

## A precise component-transport criterion

We can express both obligations without requiring an orientation-by-orientation
bijection or a new uniqueness conjecture for components. Fix a finite diagram
D and let Ω_D be its admissible selected orientations. Write F_D=Z^Ω_D for
the free module of integer multiplicities on these orientations. Choose one
direction for each actual flip edge and define its difference map by

    (B_D f)(θ→η)=f(η)−f(θ).

The kernel of B_D has as an integer basis the indicators of the ENTIRE flip
components. Thus f is an integer combination of complete component sums
exactly when B_D f=0. This includes exterior and mixed flips, not only a
local window.

For a finite family of target diagrams, let F_target be the direct sum of
their orientation modules, and B_target the block sum of their difference
maps. A signed recurrence transport is an integer linear map

    T : F_D → F_target.

**Reconstruction lemma.** T sends every source-component indicator to an
integer combination of entire target-component indicators if and only if
there is an integer matrix H such that

    B_target T = H B_D.                                (Transport)

The forward use is immediate: a component indicator is killed by B_D.
For the converse, each row of B_target T has coefficient sum zero on each
source component. Choose a root and a spanning tree in each source component.
An integer row (a_θ) with sum zero is

    Σ_(θ≠root) a_θ (δ_θ−δ_root).

Expand each difference along the chosen tree path. This expresses the row
as an INTEGER combination of source flip differences, producing the required
row of H. Isolated source vertices have zero coefficient and need no path.
No rational denominator or saturation assumption is hidden in the criterion.

Operationally, a row of (Transport) corresponds to one target flip. It says
that the difference of transported multiplicities at its endpoints is a
specified finite sum of source flip differences. A matching of occurrences
whose source labels are joined by known source flip paths supplies such a
row. This is an exact formulation of the boundary-compatibility obligation.

## Semantic transport modulo source flip differences

Fix an alphabet of size m and evaluate both models in the SAME polynomial
module: K sends each orientation to its strict order enumerator, and E sends
it to its evaluated HRV elementary monomial. Extend these maps linearly.
The weak/h convention has the same structure when used consistently.

Allow a free module F_known whose generators are independently certified
equalities K=E. A generator can be a chain state, a solved complete component,
or a solved packet. An arbitrary individual state of a solved component is
NOT a certified generator: only the complete sum was proved. If such states
are used as intermediate output, they need their own reconstruction condition.

Let R:F_D→F_known be an integer correction map and let r>0 be an integer.
The sufficient semantic certificates, for X=K and X=E, are

    r X_D − X_target T − X_known R = U_X B_D.           (Semantics)

The same combinatorial T,R,r must work for both valuations and every alphabet.
The residual maps U_K and U_E may differ and may depend on m. They record
the two separate local proofs; no pointwise matching of coloring occurrences
with HRV fibers is assumed.

**Component induction theorem.** Suppose (Transport) and (Semantics) hold,
every target component is covered by a justified smaller-diagram induction,
and every generator of F_known has its certified identity. Then every source
component satisfies K_C=E_C.

Indeed, apply (Semantics) to its indicator χ_C. The right side vanishes.
Equation (Transport) makes Tχ_C a combination of ENTIRE target components,
so target induction applies to exactly those sums. Subtract the K and E
identities; the known terms vanish as well, leaving r(K_C−E_C)=0.
Integer polynomial coefficients have no additive torsion, so r>0 cancels.
This argument covers every finite alphabet, including the empty one.

The certificate starts with r times the desired source valuation. Replacing
that left side by an unspecified mixture of unknown source components would
reintroduce an isolation obligation; it is not the same theorem. Likewise,
the matrix identities do not establish a well-founded target order. For each
actual recurrence, the diagram reduction and the status of the correction
packets must still be proved.

## How a diamond supplies the semantic certificate

Suppose source states P10 and P01 are joined by an actual flip, and their
valid diamond gives X(P10)+X(P01)=X(P00)+X(P11), separately for K and E.
Assign T(P10)=P00 and T(P01)=P11 for this local replacement. The two residuals
X(P10)−X(P00) and X(P01)−X(P11) are opposite. Their contribution for arbitrary
multiplicities f is therefore

    (X(P10)−X(P00)) (f(P10)−f(P01)).

This is a source flip difference, with the sign determined by its chosen
direction. It vanishes on every component indicator. Thus a diamond proves
(Semantics) even when either proposed pointwise equality is false. The
coloring redistribution and the HRV diamond are separate proofs of the two
opposite-residual assertions, with the SAME combinatorial replacement T.

Compositions behave well: if B₁T₁=H₁B₀ and B₂T₂=H₂B₁, then
B₂T₂T₁=H₂H₁B₀. For a unit-multiplier semantic certificate, substituting the
two semantic equations likewise expresses the composed residual through B₀,
with all certified correction terms retained. This supports building relation
(8') from relation (3) and corner branches, rather than asserting a new
pointwise swap map. Target measures and final correction packets must still
be checked for that composition.

Primary formulated these criteria after the author's clarification. Astra
independently audited the integer equivalence, semantic cancellation, and
the requirement that correction generators themselves be certified. These
criteria state what the intended recurrence proof must establish; they do
not claim that its global certificates have already been found.

## The concrete relation-(3) table to transport

The manuscript uses

    D_L = U d n V d e W,       D_R = U n d V e d W.

With the displayed lifts u<v<w<x<y<z, its distinguished data are:

| Diagram | Fixed strict edges | Distinguished normal edges, in bit order |
| --- | --- | --- |
| D_L | uw, wz | wx, xz |
| D_R | ux, xz | uw, wx |

A 1 denotes selection of the natural edge; a 0 denotes its absence from the
selected relation. The internal middle-state flip is 10↔01 on w<x<z for
D_L and on u<w<x for D_R. The proposed cross-diagram identifications are:

- 00: swap the rows and columns indexed by w and x;
- 11: use the common chain u<w<x<z after transitive closure;
- {10,01}: apply the source diamond, transport 00 and 11, and reverse the
  target diamond. Only the paired identity is required.

For the isolated four-state graphs, when all states are admissible and both
indicated flips exist, the identity bit-label map intertwines their internal
flip differences. This does not supply the semantic map for the actual
diagrams: the 00 identification changes the exterior orientation, whereas
the 11 identification keeps it fixed. We must retain that distinction.

The full diagrams add rows to B_L and B_R for exterior and mixed flips, and
may remove an internal edge when its cover condition fails. Those rows and
conditions are the next concrete proof task. They cannot be discarded by
contracting a drawn local component. Signed corrections from already solved
packets are allowed, as in the repaired five-state transfer below.

Luna re-extracted this table from the manuscript. The commented relation-(8')
sketch supplies its three branch words and four proposed cases, but its
Case-II pointwise HRV assertion fails. The paired diamond certificate above
is the appropriate replacement to test against that sketch. No manuscript
`todo` or repeated “preserving component” phrase is treated as a proof.

## Relation (3): the exterior swap and an explicit redistribution

We can locate the required redistribution in the existing Lean proof. Write
Q for a subset of the common exterior normal pairs `D.dnB e f`, and let σQ
swap the adjacent vertices w,x in every endpoint of Q. This is an involution
of the exterior powerset. The proved HRV identities are

    E_L00(Q) = E_R00(σQ),       E_L11(Q) = E_R11(Q).

Related Lean: `Circular/DNOrientationBlocks.lean`, `Diagram.dn_bottom` and
`Diagram.dn_top`. The former uses periodic swap conjugacy; the latter uses
equality of lifted transitive closures. The source and target diamonds are
`dn_source_local` and `dn_target_local`. In
`Circular/SecondBounceOrientation.lean`,
`shiftedOrientationExpansion_dnSuccessor` reindexes the ENTIRE powerset by σ
in its `hbot` step and retains Q in `htop`. This reindexing is exactly where
the aggregate argument stops tracking individual component membership.

The same endpoint identities hold for strict coloring enumerators: in the
00 case we relabel colors by the vertex swap, preserving their commutative
monomial; in the 11 case the two strict constraint relations have the same
transitive closure. These are mathematical consequences of the displayed
step conjugacy and closure proofs. They have not been exported as new Lean
orientation-enumerator declarations. They do not assert equality for either
middle state individually.

Here is a concrete family of signed transports. Let f_ab(Q) be source
multiplicities, with zero assigned to inadmissible source states, and assume
for now that

    f_10(Q) = f_01(Q) = α(Q)   for every Q.

For either valuation X, the source diamond rewrites its weighted block as

    (f_00(Q)+α(Q)) X_L00(Q) + (f_11(Q)+α(Q)) X_L11(Q).

Transport the endpoints and reindex the first sum by σ. For any integer
function β on exterior subsets, define target multiplicities by

    g_00(Q) = f_00(σQ)+α(σQ)−β(Q),
    g_10(Q) = g_01(Q) = β(Q),
    g_11(Q) = f_11(Q)+α(Q)−β(Q).

The target diamond then proves X_L(f)=X_R(g), for BOTH valuations and every
alphabet. We evaluate inadmissible states as zero and restrict g to admissible
states when asking about complete target components. This convention permits
the powerset identities to be used without silently assuming all four local
states are admissible.

The choice β=α displays the redistribution particularly directly:

    g_00=f_00∘σ+α∘σ−α,   g_10=g_01=α,   g_11=f_11.

Changing β by h changes g by h(Q)(−1,1,1,−1) in each target block. Its
valuation is zero for K and E by the target diamond. Thus β is genuine freedom
to repair component multiplicities without altering either polynomial. This
gives a concrete equation to solve: choose β, possibly together with certified
smaller correction packets, so that g has equal values across EVERY actual
target flip. It is not necessary to prescribe a pointwise middle-state map.

Two obligations remain. First, equality f_10=f_01 follows from component
membership only when those states lie in the same source component. A drawn
triangle is insufficient: `Circular/Flip.lean`, `DirectedFlipWitness`, requires
the selected short and long edges to be lifted covers on the respective sides,
and both orientations must be admissible. If these tests fail, we must retain
the unmatched term. Explicitly, setting α=f_01 gives the exact general identity

    X_L(f) = X_R(g) + Σ_Q (f_10(Q)−f_01(Q)) X_L10(Q).

Its residual vanishes for actual paired source states; the other fragments
require a separate reduction. Redundancy in one state alone does not justify
deleting a strict corner throughout its component.

Second, the free choice of β does not itself prove that the target flip
equations are consistent. Exterior and mixed flips impose equations between
different Q, and any correction packet must be independently solved and obey
the induction order. These are the concrete remaining companion lemmas for
this construction. The identities above are uniform algebraic consequences
of the actual DN endpoint maps, not a completed component recurrence.

### Nonflip blocks have exact semantic reductions

We can resolve the local unmatched-state question without treating every
triangle as a flip. Let P00 contain the selected strict long edge ac, with
lifts a<b<c<a+n; P10 adds ab, P01 adds bc, and P11 adds both. The exterior
is arbitrary and fixed. Suppose both middle states are admissible but do not
form an actual flip. At least one of the following holds:

1. P00 already has a lifted path a→b. Then P10 and P00 have identical
   reachability, as do P11 and P01. For both valuations we can replace the
   four multiplicities by `(f00+f10,0,0,f11+f01)`.
2. P00 already has a lifted path b→c. Then P01 and P00 have identical
   reachability, as do P11 and P10. The replacement is
   `(f00+f01,0,0,f11+f10)`.
3. P00 has a lifted path a→c avoiding ac. Removing the strict corner ac
   therefore preserves both valuations in all four states. We obtain a
   packet in the smaller corner-deleted diagram.

To prove exhaustiveness, a failed cover test for either selected short edge
gives the corresponding base path in (1) or (2). An alternative a→c path
in P10 either avoids ab, giving (3), or uses ab as its first edge, leaving
a base b→c path and giving (2). The argument for P01 gives (1) or (3).
All steps are positive and lie in an interval of length less than n, so no
other translate of an added edge can occur. If none of these failures occurs,
the four positive cover requirements hold. The missing-short requirements
follow from the long cover, and the two states give an actual flip witness.

If just one middle state is inadmissible, P11 is inadmissible as well. The
diamond then identifies the remaining middle valuation with P00, for K and
E separately. If both middle states are inadmissible, they carry no source
multiplicity. These cases include the projected cycles peculiar to circular
diagrams; we do not infer admissibility from the drawn lifted triangle.

Thus every local block can be reduced to a paired flip block, endpoint
terms, or a smaller corner-deletion packet. This is a proved semantic
classification, independently supplied and checked by Astra and primary.
It leaves a global reconstruction problem: a deletion packet need not be a
complete smaller component, and eliminating middle multiplicities can change
their compatibility with exterior flips. The target parameter β and the
deleted packets must be handled together.

### Reconstruction as an integer potential problem

For the family g above, we can state the remaining equations without a
general integer-matrix solve. Put

    A(Q)=f00(σQ)+α(σQ),       B(Q)=f11(Q)+α(Q),
    γ(Q)=(-1)^|Q| β(Q).

For an admissible target state θ with exterior Q and t selected distinguished
pairs, define b(θ)=A(Q) for t=0, b(θ)=0 for t=1, and b(θ)=B(Q) for t=2.
Its total normal ascent count is k=|Q|+t. The multiplicity formula becomes

    g(θ)=b(θ)−(-1)^k γ(Q).

An actual target flip θ↔η preserves k. Consequently equality of transported
multiplicities across this flip is exactly

    γ(Q_θ)−γ(Q_η)=(-1)^k (b(θ)−b(η)).             (Potential)

This uses signed integer multiplicities; no nonnegativity bounds on β are
required. In particular, a flip toggling one distinguished pair also toggles
one exterior pair, changing |Q| by one. A flip toggling both distinguished
pairs has local type 10↔01 and leaves Q unchanged. If neither toggled pair
is distinguished, the local bits stay fixed and |Q| is unchanged. The type
00↔11 is impossible because a flip removes one pair and adds one pair.
These facts explain why the apparent sum equations for β become difference
equations for γ.

Construct a finite multigraph with exterior subsets as vertices and one edge
Q_θ→Q_η for each actual target flip. We retain parallel edges and loops, and
label that edge by the right side of (Potential). Reverse traversal negates
the label. Then an integer β making g constant on ENTIRE target components
exists if and only if the labels sum to zero along every closed walk.

Necessity follows by telescoping γ. For sufficiency choose a root and spanning
tree in each connected component of the multigraph. Set γ at the root to
zero and extend using (Potential) on tree edges. The closed-walk condition
makes each remaining edge consistent. All labels are integers, so this gives
integer γ and hence integer β, with no divisibility assumption. Loops require
zero label; parallel edges impose their corresponding two-edge condition.
Only flips between admissible target states enter the graph. Isolated
exterior subsets impose no condition and may be assigned γ=0.

We must include cycles that switch ascent levels at a shared Q: the same
potential controls its zero, middle and full states. Checking the constraint
graph separately at each ascent would miss these conditions.

This is an exact reconstruction criterion for the displayed DN transport
family. It turns the global obligation into a concrete companion lemma:
prove that these closed-walk sums vanish for source-component multiplicities,
after retaining the nonflip reductions and any certified correction packets.
The potential argument does not prove that vanishing. With fixed trees, its
construction is integer-linear in the source multiplicities whenever the
compatibility conditions hold, as required by the earlier transport interface.
Equivalently, each fundamental-cycle period row must be an integer combination
of source flip-difference rows. This follows from the same spanning-tree row
argument used in the reconstruction lemma. Primary derived the potential
formulation; Astra and Luna independently checked the parity change and
cycle criterion, including admissibility and the shared ascent levels.

### Exterior flips at the two endpoint states

Two classes of potential equations follow from actual flip-graph maps, not
just polynomial identities. We retain all hypotheses of `dnSuccessor`.

**Zero stratum.** The involution Q↦σQ identifies the induced flip graphs on
source and target 00 states. Indeed, `dn_swap_step` conjugates the full
selected lifted step relations, preserving reachability, covers and projected
admissibility. `dnB_map_swap` carries the two exchanged exterior normals to
exterior normals. A flip preserving 00 cannot use both swapped residues w,x:
the forward adjacent pair wx is absent, while `hb` excludes the reverse
length-(n−1) pair xw. Such a reverse pair cannot be a short in a window of
length less than n either. Therefore the periodic swap preserves the order
of the flip triangle. The retained selected long maps to a selected natural
edge by the step conjugacy. This constructs the flip witness in both
directions, using involutivity.

**Full stratum.** The identity on Q identifies the induced flip graphs on
source and target 11 states. The proof of `dn_top` gives equality of the full
lifted transitive closures. The source-only long wz is redundant through
w→x→z; the target-only long ux is redundant through u→w→x. Neither can be
a retained cover. Every other selected pair agrees. Thus the exterior short
edges remain normal on both sides, the retained cover long exists on both,
and all source and target cover tests agree. Equality of lifted reachability
also preserves projected admissibility.

Consequently an ORIGINAL source-component indicator satisfies

    f00(σQ)=f00(σQ') on a target 00↔00 flip,
    f11(Q)=f11(Q')   on a target 11↔11 flip.

In the paired-block formula, these equations reduce the endpoint constraints
to constancy of β−α∘σ along the target zero-stratum flips, and of β−α along
the full-stratum flips. Preprocessing a nonflip block changes multiplicities;
we must retain its correction terms before applying such original-component
constancies. The assertions above concern induced subgraphs, not complete
components of the full diagram.

There is also a geometric restriction on mixed flips. The target normal
uw can only be toggled against wx in the internal 10↔01 flip. It was a maximal
natural corner in the source; the only newly added natural interval containing
it is ux, and x=w+1. Dually, the source normal xz can only be toggled against
wx. To justify this second statement, use the eligible-DN gap `hgap`: the
source left boundary is w at z and at least w+2=x+1 at z+1, and is nondecreasing
on the integer cover. A natural interval containing [x,z] must therefore end
at z and start at w or x. Its only proper containing interval is wz.

It follows that target mixed flips have only types 00↔01 and 11↔10; source
mixed flips have only types 00↔10 and 11↔01. These restrictions include wrapped
intervals because the argument uses integer lifts. The strict-corner condition
alone would not suffice for the source xz restriction without `hgap`.
Primary and Astra independently checked these maps and their hypotheses.
They are prose proofs using the existing Lean geometry; no new Lean flip-map
declarations have yet been compiled. Mixed-state period cancellation and the
regrouping of deletion packets remain separate obligations.

### An ordinary linear residual, and why it cannot be held fixed

For ordinary diagrams we can remove the paired-multiplicity hypothesis from
the semantic formula. Keep the ORIGINAL source-component multiplicities f
and put δ(Q)=f10(Q)−f01(Q). Let D_del be the source with its strict long wz
deleted. For arbitrary β define

    g00(Q)=(f00+f01)(σQ)−β(Q),
    g10(Q)=g01(Q)=β(Q),
    g11(Q)=f11(Q)+f10(Q)−β(Q),
    R=Σ_Q δ(Q)([del00(Q)]−[del01(Q)]).

Then, for BOTH valuations and every alphabet,

    X_L(f)=X_R(g)+X_del(R).                           (Ordinary residual)

To prove it, the endpoint maps and target diamond give
X_R(g)=Σ_Q((f00+f01)X_L00+(f11+f10)X_L11). Subtracting this from the source
sum and using its diamond leaves δ(Q)(X_L00−X_L01) in each block.
The short wx has length one, so it cannot be implied by a base alternate path.
If the two middle states flip, δ=0. If xz is already implied, its witness
cannot use wz because all steps are positive and w<x. Thus both the source
and deleted contrasts vanish. Otherwise the nonflip classification makes wz
redundant in the base, so the source and deleted contrasts agree. This proves
the formula with R summed over ALL Q, without a case-dependent indicator.
We use ordinary acyclicity here; the circular one-cyclic-middle cases require
an additional argument and are not included in this lemma.

This formula is linear and supplies actual semantic transport. It does not
prove reconstruction. In fact, keeping this R fixed leaves the target
equations inconsistent in the already-recorded saturated five-state source
component C={abc,abd,bcd,bde,cde} below. Use its notation
a=23,b=24,c=34,d=35,e=45, with local bits a,d. Set

    Q1={24,34},       Q2={24,45}.

The target states {23,24,34} and {23,24,45} are both middle states and are
joined by the actual flip at 3<4<5 retaining strict35. Equality of g therefore
requires β(Q1)=β(Q2). Adding the target normal12 gives full states
{12,23,24,34} and {12,23,24,45}, still joined by that same flip. However,
the full-state endpoint coefficient f11+f10 equals 1 at Q1 and 0 at Q2:
source abc belongs to C, source abe does not, and both f11 terms vanish by
ascent. Equality of the two full-state multiplicities instead requires
β(Q1)−β(Q2)=1. This is a two-edge nonzero period involving different ascent
levels, not a failure of the proved potential criterion.

Therefore the deletion packet must be allowed to change together with the
target multiplicities. A different β with this fixed packet cannot suffice.
This does not refute the earlier paired-block construction, whose hypothesis
f10=f01 this C does not satisfy, or the author's component recurrence route.
Indeed, the same diagnostic has the proved complete-component identity
X_C=X_D−e5. Primary and Astra independently checked both the ordinary residual
lemma and the explicit two-edge contradiction.

### A common diagram for the two deletion packets

Let e=uw, f=wz, e'=ux and r=xz. Source-delete(f) and target-delete(e') have
the SAME natural graph G0: the DN move removes the natural pair f and adds
e', and the second deletion removes e' again. Their strict sets are S0∪{e}
and S0∪{r}, respectively, where S0 contains the unchanged strict edges.
Let H have natural graph G0 and strict set S0.

Both e and r are unmarked natural corners of H. Deleting f leaves the two
area entries defining the e-corner unchanged: the head z is neither w nor
x=w+1 because f has length at least two and less than n. On the target side,
r is a surviving strict corner after deleting e'; their heads z and x are
distinct. Unstricting a corner leaves its natural-corner property unchanged.
These statements use the full eligible-DN hypotheses that made the target
valid, including `hgap`. The description works on the circular integer cover
as well. In Lean it requires the corner inclusion/restriction identifications
between dependent edge types, rather than literal equality of edge terms.

Since e and r are natural corners, their selected statuses are invariant on
EVERY complete H component. Thus source-delete(f) identifies with the entire
e-selected sector of H, and target-delete(e') with the entire r-selected
sector. These are unions of complete components. The intersection where
both corners are selected is the same selected relation on both sides,
preserving colorings, covers and HRV data pointwise.

There is no induction circularity in using complete H components as known
packets. Deleting the strict corner f lowers doubled area by one; unstricting
e raises it by one. Therefore H has the same doubled area as the source D.
For any component of H, resolve its invariant e-status: strictification gives
a diagram of doubled area `doubledArea D−1`, while deletion gives one of
area `doubledArea D−2`. The exact corner-branch correspondence identifies the
ENTIRE component with one in the chosen smaller diagram. Hence smaller-area
component induction supplies all H component identities. Resolving both
unmarked corners gives four smaller sectors if the two-sided bookkeeping
requires them.

This supplies a common component space in which to recombine deletion terms.
It does not say that an arbitrary packet already has component-constant
multiplicities. In particular, the two sides use different sectors of H;
only their both-selected parts can be transferred directly. We must still
construct the joint redistribution and any corrections by complete solved
components. Primary and Terra checked the geometry, corner-status invariance
and strict measure decreases. This is a component-level reduction under the
stated induction hypothesis, not an application of the aggregate identity.

## The coloring redistribution is explicit

Let P00 contain a<c, with arbitrary fixed exterior relations. Let P10 add
a<b, P01 add b<c, and P11 add both. For weak colorings of P00 set
A := [f(a) ≤ f(b)] and B := [f(b) ≤ f(c)]. Since f(a) ≤ f(c), A or B holds.
Consequently

    1_A + 1_B = 1 + 1_(A and B).

This gives a monomial-preserving bijection between the disjoint unions of
colored occurrences for {P10,P01} and {P00,P11}. Send a P10 coloring to P00.
Send a P01 coloring to P11 if A holds, and otherwise to P00. Inverting this
map uses A to decide the preimage of a P00 coloring; a P11 coloring returns
to P01. Every vertex keeps its color. Exterior constraints remain satisfied
because the coloring itself is unchanged.

The same construction works for strict colorings: f(a)<f(c) ensures
[f(a)<f(b)] or [f(b)<f(c)]. The common-base/four-state description must hold
for the actual diagrams, not just their drawn internal edges.

The separate HRV diamond identity matches the multiset of HRV partitions
on the two sides. It requires the actual lifted reachability hypotheses.
This yields both valuation identities without asserting a pointwise HRV
match for the coloring map. The manuscript's false pointwise step in the
commented (8') sketch should stay excluded.

## Do not impose ascent preservation on the unweighted target

The component conjecture K_C=H_C is unweighted. The ascent number is constant
inside a component, but an induction proving all component identities may
use target components at different ascent numbers. The diamond itself takes
two k-ascent states to a (k−1)- and a (k+1)-ascent state.

This narrows the obstruction in the current notes. For the displayed ordinary
relation-(3) instance X=ndnndeee and Y=nndnedee, the source vector is

    H_C = h_(3,2) + 2 h_(4,1) + 2 h_5.

Its failure to lie in the rational span of the three displayed target vectors
is a failure of the SAME-ASCENT span. It does not rule out target components
at other ascents. In Y, the fully ascending orientation contains the entire
adjacent chain, hence has a total-chain poset. It is the unique maximal-ascent
orientation, so its complete component T is a singleton with K_T=H_T=h_5.

The manuscript records, for its six-state target component D,

    K_D − K_C = h_5,    H_D − H_C = h_5.

The coefficient proof below now establishes the recorded K identity as well
as the H identity. This gives the simultaneous target-only identity

    X_C = X_D − X_T,    X in {K,H}.

Thus this particular obstruction is repaired using complete TARGET components
at different ascents. This is a checked mathematical proof, not yet a Lean
formalization. The second recorded obstruction is also repaired below: its
two components belong to different branches of a single corner split.

For an argument retaining the aggregate q-weight, exponent changes must be
accounted for explicitly. For the component identity itself we can work
unweighted and retain each separate local equality before combining them into
one polynomial recurrence. Specializing an aggregate identity alone would
lose this component information.

## Exact corner branching and the selected-edge envelope

A natural corner edge cannot be a toggled short edge of a flip: the retained
long edge would require a natural cell above it in its column or to its left
in its row. The same argument applies to every integer translate. Its selected
status is therefore constant on an ENTIRE component.

If it is absent, delete the corner. If it is present, make it strict. Both
operations preserve the selected relation exactly, including all integer
lifts. They preserve admissibility, cover tests, and every flip in both
directions. Thus each branch carries entire components, with their actual
coloring and HRV semantics. Strictification removes one counted normal ascent;
this accounts for the factor t in the aggregate corner recurrence.

Repeating this procedure removes all unselected outer cells and leaves the
interval envelope generated by the selected edges. This envelope is invariant
under flips: the new short edge is inside the retained long edge. Every corner
of the resulting envelope is selected and can be made strict. There is no
claim that fixed ascent determines a component in this saturated diagram;
the first diagnostic below disproves that stronger assertion.

## General reduction: an always-redundant strict corner

**Proved mathematically; not yet formalized.** Let e be a strict corner of D
and C a complete component. Suppose that in EVERY state A of C the natural
lift of e is not a cover. Equivalently, its endpoints are joined by a selected
lifted path not using e. Then deleting e identifies C with an ENTIRE component
of `D.deleteCorner e`, preserving full lifted reachability, coloring enumerators,
and actual HRV monomials state by state. The normal ascent count is unchanged;
the doubled geometric area decreases by one. Thus smaller-area component
induction proves the identity for C.

We prove the claim for the manuscript's actual lifted-cover flips, including
circular diagrams. There are three points to check.

1. A natural corner interval cannot be properly contained in another natural
   edge interval. A path testing the cover of any other natural edge therefore
   cannot use any translate of e: positive steps keep that entire path inside
   the tested interval. Deleting or inserting e does not change any OTHER
   natural-edge cover test. It also cannot toggle e, which is a corner.

2. The union of the selected relations of two admissible flip states is
   projected acyclic. A simple cycle in the union would have to use both
   exchanged edges ab and bc; either one alone belongs to an acyclic endpoint
   state. They must be consecutive on the simple cycle. Replacing them by
   the retained edge ac gives a cycle in both endpoint states, a contradiction.
   Now start with A in C and its image B=A without e. Given any target flip
   B to B', this union is acyclic. The alternative path for e is contained
   in B, so adjoining e to B union B' leaves its reachability unchanged.
   In particular A'=B' plus e is admissible. All the required cover tests
   agree by point 1, so this is a genuine source flip A to A'.

3. Since A' is reached by a source flip, A' belongs to C. The hypothesis on
   the WHOLE component supplies the alternative lifted path for e again.
   Induction along any target flip path therefore constructs its preimage
   in C. Conversely, a source flip in C uses e neither as a short edge
   (it is a corner) nor as its retained long cover (it is noncovering).
   It consequently deletes to a target flip. Insertion/deletion are inverse,
   proving the correspondence with complete components, not just fragments.

Finally, substitute the alternative path for every use of every translate of e.
This proves equality of full lifted reachability on each matched pair.
The projected order constraints and reachable maxima agree, giving both
semantic identifications. This is stronger than projected redundancy alone;
an alternative path ending one period later would not justify the lemma.

Primary and Astra independently checked the reconstruction, including the
acyclicity of reinserted target states. The whole-component hypothesis is
essential: a corner can be redundant at one state and covering at a neighboring
state. In the first diagnostic all three ancillary source components satisfy
the hypothesis for corner 25, but C does not. Their separate base calculations
can therefore be replaced by this general smaller-area reduction.

Related Lean: `Circular/CornerPairs.lean` exports
`deleteCorner_naturalPairs` and `deleteStrictCorner_pairGraph_normalEdges`;
`CornerDeleteOrientation.lean` has the edge inclusion/restriction maps.
`LiftCover.lean`, `Flip.lean`, and `HRVPotential.lean` supply the actual lifted
covers, complete component relation, and HRV transport interfaces. Luna audited
these APIs without building. The existing `orientToDelete` and
`orientFromDelete` require a NONSTRICT corner, so they do not yet implement
this theorem. Also, `D.liftStep (theta.val.erase e)` does not delete a strict e:
`liftStep` always includes `D.strict`. The alternative-path hypothesis must use
the deleted diagram's transported selection or a relation explicitly filtering
out e. There is no global equivalence of all target/source orientations;
reinsertion is justified along the particular component by the proof above.

## Ordinary corner deletion as an exact component quotient

There is a stronger structural statement in the ordinary case. Let e be a
strict corner, without requiring it to be redundant. All orientations of D
identify with orientations of D-e by removing the fixed edge e: all ordinary
selected relations are acyclic and the normal edge set is unchanged.

Under this identification, the flip graph of D is exactly the flip graph
of D-e with the valid flips retaining e as their long edge added. The earlier
corner-interval argument shows that e affects no other natural-edge cover
test. It cannot be a toggled short edge. Thus all old target flips lift, and
the only additional source flips are precisely those supported by e.

Contract each COMPLETE component of the smaller diagram to a vertex, and
keep an edge whenever an e-supported source flip joins two such components.
The connected components of this quotient graph are exactly the complete
source components. Exposure of every OTHER strict corner is preserved
pointwise by deletion. This is an actual graph statement, not a proposed
matching of local-state tables. It must not be extended to arbitrary circular
orientations without checking admissibility of reinsertion.

This quotient also gives a useful exact equation for component defects.
Write Δ_D(A)=K_D(A)−E_D(A), and assume the component identity is proved in
D-e. Since a complete source component C is a union of complete deletion
components, we have Σ_(A∈C) Δ_(D-e)(A)=0. Whenever e is redundant,
Δ_D(A)=Δ_(D-e)(A). Subtracting therefore gives

    Δ_D(C) = Σ_(A∈C, e is a cover) (Δ_D(A)−Δ_(D-e)(A)).

This equation localizes the remaining defect on the cover states without
asserting that the redundant fragments form components. It is proved for
ordinary diagrams by the graph quotient above and smaller-area induction.
Cancellation or recurrence for this boundary sum remains to be established.

For an actual flip supported by e, put B_ij=A_ij-e and
δ_ij=Δ_D(A_ij)−Δ_(D-e)(B_ij). The source diamond and redundancy in state 11
give the exact boundary relation

    δ_10+δ_01 = δ_00+Γ,
    Γ = Δ_(D-e)(B_00)+Δ_(D-e)(B_11)
        −Δ_(D-e)(B_10)−Δ_(D-e)(B_01).

We must retain Γ. The long edge was removed in D-e, so its four states do
not inherit the same diamond identity. Smaller-area induction cancels a sum
of these residuals only after the signed coefficients reconstruct complete
deletion components. Corner leaf-normalization supplies valid flip paths;
it does not, by itself, prove this multiplicity statement or make the boundary
relation telescope. Primary and Astra independently checked the boundary
equation and this distinction.

For e=(a,a+2), there is only one supporting triangle. Its adjacent short edges
are automatically covers when selected; e is redundant precisely in state 11.
The additional quotient edges therefore come from exactly the unconditional
10-to-01 swaps on those shorts, with arbitrary fixed exterior selection.
Deleting e makes a+1 an articulation of the natural graph: any other edge
crossing it would properly contain the maximal corner interval e.

The short edges need not themselves be corners after deletion, so exterior
flips can change their status. This gives a smaller-block connectivity problem,
not an independent cube decomposition. Proving the requisite connectivity of
active quotient classes remains open. The newly proved endpoint/gluing theorem
in `COMPONENT_ENDPOINT_GLUING.md` supplies the separate block-count aggregate
identity needed once such structural isolation is established.

## Diagnostic certificates: the two recorded bounce obstructions

These are repairs of existing proof obstructions, not substitute targets for
the full component theorem. We use one-based labels and weak/h notation.
The same diamonds give strict/e identities, with no appeal to the conjecture.
Primary and the independent Astra reviewer checked both certificates.

### The five-state source and six-state target

For X=`ndnndeee`, let a,b,c,d,e denote normal edges 23,24,34,35,45;
the strict edges are 12,25. Its complete ascent-three components are

    C = {abc,abd,bcd,bde,cde},
    S1 = {acd,ade}, S2 = {abe,bce}, C0 = {ace}.

For Y=`nndnedee`, let A,B,C,D,E denote normals 12,23,24,34,45;
the strict edges are 13,35. Its complete ascent-three components are

    D = {ABC,ACD,ACE,BCD,BCE,CDE},
    T1 = {ABD,ABE}, T2 = {ADE,BDE}.

These lists exhaust all ten three-element normal selections on each side;
the actual cover flips give exactly the listed components. Each of S1,S2,
T1,T2 is a two-state diamond whose zero state is a four-chain plus an isolated
vertex, and whose full state is a five-chain. The triangles are respectively
345,234,345,123. Consequently each has valuation h41+h5, for BOTH valuations.
C0 is a five-chain, so its valuation is h5.

Taking the ascent-three coefficient in the proved DN recurrence gives

    X_C + 2(h41+h5) + h5 = X_D + 2(h41+h5),  X in {K,H}.

Cancelling the solved terms proves X_C+h5=X_D. This uses only aggregate
recursion and independent diamond/chain proofs, not the component identity
for either C or D. The singleton maximal-ascent target supplies the same h5
correction, giving a signed formula entirely in target components.

X is already saturated: its only natural corners are the two strict edges.
All ten states have connected underlying selected graphs on five vertices.
Thus saturation, ascent, and weak connectivity together do not imply that
these states form one component. The recurrence succeeds by eliminating
independently solved source components.

### The two four-state components: split corner 24 first

In Y=`nndnedee`, use lower-case a,b,c,d,e for 12,23,24,34,45.
At ascent two its components are

    C1 = {ac,bc,cd,ce}, C2 = {ad,ae,bd,be}, {ab}, {de}.

Crucially, 24 is an unmarked NATURAL CORNER. Every state of C1 selects it,
whereas every state of C2 omits it. The corner recurrence therefore puts C1
in the strictification branch and C2 in the deletion branch. The eight-state
merger under the unrestricted bounce ignores this useful branch information.

C2 is the product of the diamonds 123 and 345, with 24 absent. Resolve the
first diamond for each state of the second, then resolve the second for each
zero/full state of the first. The four resulting posets are disjoint unions
of chains, of types 311,41,41,5. All exterior edges are retained. Hence

    K_C2 = H_C2 = h311 + 2h41 + h5.

The singletons ab,de each give h41. Consequently the ascent-two aggregate
bounce equation to `nnndeede` isolates C1 after the target components and
these independently solved source terms are handled. This removes the
second recorded same-ascent obstruction; no assertion that arbitrary source
components transport individually is required.

## A full family of independently solved corrections

Take vertices v0<...<v_(2k), retain the k spine edges v_(2i)->v_(2i+2),
and in each triangle choose exactly one of its two short edges. These 2^k
states form an ENTIRE component, even in the complete ordinary ambient graph.
Their selected-edge envelope contains just those consecutive triangles;
every flip stays in it. The only possible flips switch the independent short
choices. No other triangle or cover condition introduces extra states.

Resolve all k diamonds. A subset J of full states gives one chain of length
k+1+|J| and k-|J| isolated middle vertices. Thus both component valuations are

    sum_(j=0)^k binom(k,j) h_(k+1+j) h1^(k-j).

The empty case k=0 is included. Disjoint products with independently solved
components preserve the identity. This is a uniform proved family of source
corrections. It does not assert that all correction components are of this form.

## Remaining construction and verification

The transport criterion at the start of this note replaces the earlier
informal reconstruction/isolation checklist. For each actual recurrence,
construct T and the certified correction map R from the local cases, then
check every target-flip row of (Transport) and both versions of (Semantics).
The target diagrams must decrease a justified induction measure. The ordinary
and circular component conjectures remain open until these constructions
are supplied; the criterion alone does not prove them.

The previously proposed fixed-diagram diamond-and-chain straightening theorem
is false, even with signed rational coefficients. Its exact obstruction,
auxiliary-state repair and exterior-swap correction remain in
[the diamond audit](DIAMOND_STRAIGHTENING_AUDIT.md). It is not an active target.
The squared-ascent statistic does terminate forward diamond replacements,
but terminal multiplicities need not be constant along flips. It therefore
does not supply the reconstruction certificate either.

Related Lean: `Circular/Flip.lean` and `Circular/ComponentSemantics.lean`
fix the actual graph and complete-component sums. The new transport criterion
and the mathematical corner reductions in this note are not yet implemented.
Keep examples and finite diagnostic certificates separate from any claimed
uniform recurrence map. No generic Lean scaffolding should substitute for
the missing map and its global boundary proof.

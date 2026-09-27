# Corner differences and signed component recurrences

Status: the ordinary quotient, inclusion–exclusion recurrence, and relative
absorption identities below are proved mathematical statements. They are not
Lean declarations. The general component HRV theorem remains open.

We use K(A) for the strict coloring enumerator and E(A) for the evaluated
HRV elementary monomial of a selected relation A, on one fixed finite alphabet.
These are unweighted state contributions. Component sums need no ascent
factor; a normal ascent factor common to a component can be restored later.
Write Δ=K−E. All ordinary edges increase in the fixed vertex order.
The [induction note](FLIP_COMPONENT_INDUCTION.md) owns minimum-area realization
and the general signed packet criterion.

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

## Alternating deletion of several strict corners

Let D be an ordinary decorated diagram, S its strict corners, and F⊆S.
For T⊆F let D\T be the diagram obtained by deleting those strict corners.
Each deletion is valid: removing a maximal natural interval leaves every
other strict corner maximal. The normal edge set stays unchanged, and

    doubledArea(D\T) = doubledArea(D) − |T|.

All normal selections are admissible in the ordinary case. We identify their
state sets by their normal selections, inserting the appropriate remaining
strict edges. The flip graph of D\T is a spanning subgraph of the source
flip graph: it deletes exactly the flips retaining a corner in T. Indeed,
no alternate path testing another natural edge can use a deleted corner,
since such a path lies inside the tested interval and the deleted interval
is maximal. Nor can a corner occur as an exchanged short edge.

Consequently every COMPLETE source component C is a disjoint union of
COMPLETE components of D\T under this identification. Denote this partition
by P_T(C). This is the reconstruction step; it uses ordinary admissibility,
not just a statewise polynomial identity.

For X=K or E define the alternating corner difference

    ∂_F X(A) = Σ_(T⊆F) (−1)^|T| X(A\T).

If one corner s∈F is redundant in A, choose a selected alternate path between
its endpoints. That path lies inside s, so it contains no other strict
corner. It therefore survives the deletion of ANY subset of F\{s}.
Pair T and T∪{s} in the alternating sum. Deleting the redundant s preserves
all reachability, hence both the strict coloring constraints and every highest
reachable vertex. The two terms cancel. Thus

    some s∈F is noncovering in A  ⇒  ∂_F K(A)=∂_F E(A)=0.

### A signed recurrence in whole smaller components

Suppose no state of C has all corners in F covering simultaneously. Then
for BOTH valuations, with exactly the same integer coefficients,

    X_D(C) = Σ_(∅≠T⊆F) (−1)^(|T|+1)
                         Σ_(C'∈P_T(C)) X_(D\T)(C').

Proof: sum the preceding vanishing over A∈C, move the empty-deletion term
to the other side, and use the proved whole-component partition P_T(C).
Every right-hand diagram has strictly smaller doubled area. This proves the
component identity for C under smaller-area induction. The corner which is
redundant may depend on A; no single corner need be redundant throughout C.

More generally, assume smaller-area component identities without imposing
the simultaneous-cover hypothesis. Every nonempty deletion sum of Δ vanishes
by that induction, so

    Δ_D(C) = Σ_(A∈C) ∂_F Δ(A)
           = Σ_(A∈C, all corners in F cover) ∂_F Δ(A).

Taking F=S proves a stronger necessary condition for a minimum-area ordinary
counterexample: it contains ONE state in which ALL strict corners are covers.
The earlier condition asked only for a possibly different witness at each
corner. This does not prove the formula for components with a common witness.
For S empty the conclusion is vacuous and the recurrence has no reduction.

Primary, Astra and Terra independently audited this argument. It directly
implements signed induction on the author's minimum-area realization, without
assuming uniqueness of an active component or of a component in a DN packet.
Known components removed from a packet may now include this larger class.

## A stronger companion: mixed-cycle cancellation

We can replace the single redundant-corner witness by a directed cycle using
several reversed corners. The HRV cancellation holds at the level of its full
reachable-maximum map, which makes it independent of elementary evaluation.

Let N and F be disjoint sets of strictly forward edges on a finite linearly
ordered vertex set. They need not form a diagram, and F need not be corners.
For J⊆F let α_J(v) be the greatest vertex reachable from v in N∪J, including
v itself. Suppose the mixed directed graph N∪F^op has a directed cycle,
where F^op reverses every edge of F. Then, in the free abelian group on maps,

    Σ_(J⊆F) (−1)^|F\J| [α_J] = 0.

In particular, applying the HRV elementary evaluation gives ∂_F E(N∪F)=0.
For K, inclusion–exclusion gives

    ∂_F K(N∪F) = (−1)^|F| · K_mixed(N,F),

where K_mixed enumerates colorings strict along N and weak along F^op.
Any mixed cycle contains an N-edge, because reversed forward edges alone
strictly decrease. Its color inequalities therefore contradict themselves,
so the coloring difference also vanishes.

### An involution preserving the entire HRV map

Fix a simple mixed cycle, independent of J. Write its reversed distinguished
edges as h_i→t_i, with fixed N-paths t_i→h_(i+1) between them, cyclically
indexed. An N-path may be empty. There is at least one distinguished edge.
Given J, choose the cycle head h_j maximizing the pair (α_J(h_j),h_j)
lexicographically, and toggle f=t_(j−1)→h_(j−1) in J. Heads on the simple
cycle are distinct, so this is a deterministic choice. Write

    t=t_(j−1), h=h_(j−1), M=α_J(h_j).

The fixed N-path gives α_J(t)≥M, and the chosen maximum gives M≥α_J(h).
If f is absent, adding it cannot increase any reachable maximum: the new
edge only gives t access to vertices no larger than its existing maximum.
The same holds for all predecessors of t.

If f is present and α_J(t)>M, a path realizing that maximum cannot use f,
since every vertex reachable after f is at most α_J(h)≤M. If α_J(t)=M,
use the fixed N-path t→h_j followed by a path realizing α_J(h_j)=M.
The suffix cannot use f unless h_j≤t; the fixed prefix gives t≤h_j.
Thus use of f would force t=h_j. Its head h is then strictly greater than
h_j, and M reachable from h implies α_J(h)=M. This contradicts the
rightmost-head tie-break. We have therefore exhibited a maximal path from
t avoiding f in every case. Every predecessor whose old maximal path used
f can reroute through this path, preserving its maximum as well.

The whole vector α_J is unchanged under the toggle. Hence the chosen head
and edge are unchanged, and this operation is an involution. It reverses
the sign and pairs equal maps, proving the identity. Astra supplied this
argument; primary and Terra independently audited addition, deletion, empty
path segments and the stability of the chooser. No Lean check is claimed.

### Stronger signed recurrence and remaining support

Return to an ordinary diagram, complete component C, and strict F⊆S. For a
state A put N=A\F, retaining the other strict edges as forward base edges.
If EVERY A∈C has a directed cycle in N∪F^op, then the SAME signed recurrence
in complete smaller components from the preceding section holds. Both
alternating state valuations vanish by the mixed-cycle companion, and the
ordinary deletion quotient supplies exactly the same reconstruction.

Under smaller-area induction, without assuming this cycle condition,

    Δ_D(C) = Σ_(A∈C, (A\F)∪F^op acyclic) ∂_F Δ(A).

Thus, with F=S, a minimum-area ordinary counterexample must contain a state
whose selected normals together with REVERSED strict corners are acyclic.
This implies the earlier common-cover condition: any alternate forward path
for a strict corner would close a mixed cycle with its reversal. The converse
need not hold. For example, on vertices 1,...,5 with strict corners 14,25,
the normal selection {13,35,24} leaves both corners covering, but the mixed
graph contains 4→1→3→5→2→4. This is a diagnostic for the distinction between
the two support conditions, not a counterexample to the component theorem.

The [exact HRV-map coefficient formula](COMPONENT_HRV_DIFFERENCES.md)
now replaces the alternating HRV sum by explicit coefficients in {−1,0,1};
at each fixed map its component coefficient is a signed count of normal
selections with specified outgoing support. This is an exact refinement of
the remaining semantic problem.

The [strict-chain normalization](COMPONENT_CHAIN_NORMALIZATION.md) now gives
every such state a deterministic representative reached through actual flips,
and its fibers are connected. Different representatives still interact within
one complete component.

The remaining task is to handle entire components having such an acyclic
state. Neither the support restriction nor the involution provides the
missing whole-component recurrence for that class. In particular, a subset
of acyclic mixed states need not itself be a union of flip components.

## Relative absorption of incoming edges

Fix an ordinary strict corner f=wz and a selected normal edge aw with a<w<z.
Put P=A\{f,aw}. Suppose P has a selected path a→z. Then

    ∂_f X(A) = ∂_f X(A\{aw}),     X=K,E.

For K, the difference K(A)−K(A\{f}) is the negative enumerator of colorings
satisfying the remaining edges and violating c(w)<c(z). The path in P gives
c(a)<c(z)≤c(w). Hence the aw constraint is automatic in this difference,
which proves the identity.

For E, let H_v be the largest vertex reachable from v in P, including v
itself. We have H_a≥H_z. If H_w≥H_z, adding f changes no reachable maximum,
either before or after adding aw. If H_w<H_z, adding aw changes no reachable
maximum, either before or after adding f: even then the largest vertex newly
reachable through w is at most H_z≤H_a. These statements also hold for every
predecessor of a or w. The four elementary contributions therefore satisfy

    E(P+f+aw) + E(P) = E(P+f) + E(P+aw).

This proves the relative identity with arbitrary exterior selected edges.
It requires neither a direct selected az edge nor any cover hypotheses.

### A deterministic idempotent state projection

Let P_f(A) erase every selected NORMAL incoming edge aw for which a reaches z
in A\{f}; keep all strict edges. Then, in an ordinary diagram,

    ∂_f X(P_f(A))=∂_f X(A),     P_f(P_f(A))=P_f(A).

If f is a cover, every such witness path avoids all incoming edges into w.
Otherwise its suffix after reaching w would be an alternate w→z path.
All witnesses consequently survive simultaneous erasure; each erasure is
justified by relative absorption. Removing incoming edges does not alter
covering of f. It cannot create new eligible edges, proving idempotence.

If f is not a cover, its alternate w→z path uses no incoming edge into w
and survives. Every selected normal aw is eligible via this path, so all
are erased. The relative valuations are zero both before and after, and
idempotence again follows.

This projection may lower the normal ascent count. It is a state operation,
not a map between whole components. Constancy of its pushforward multiplicity
on target components, even after redundant-state corrections, is UNPROVED.
A pointwise relative identity does not permit induction on individual images.
The E argument uses the linear order of ordinary reachable maxima. A projected
circular path to the residue of z need not end at the correct integer lift;
no circular version is asserted here.

### The double-attachment crossing boundary

Let f=wz and g=ab be strict corners, a<w<b<z. Suppose bz is selected and aw
is an optionally selected normal edge. Set

    A = Q+{f,g,aw,bz},       C0 = Q+{f,g,bz}.

The path a→b→z uses g and bz, so relative absorption gives

    X(A)−X(A\{f}) = X(C0)−X(C0\{f}),     X=K,E.

Equivalently, apply the g-long diamond before and after deleting f. The other
two states have wb and bz selected, so f is redundant in both and their
f-differences vanish. This proof also needs no exterior cover assumptions.
It handles the double-attachment case excluded by the
[crossing sweep](DN_COMPONENT_COMPLETION.md#preconditioning-a-crossing-corner-flip)
at the level of relative valuations.

With several fixed crossing longs a_i b_i and selected b_i z, the same
identity holds throughout the Boolean cube of optionally selected normal
edges a_i w. All witness paths remain present. This still does not establish
whole-component regrouping of the cube's occurrences.

There is a precise caveat when combining this with full-corner differences:
the witness path used the strict corner g. For the full strict set S,

    ∂_S X(A)−∂_S X(C0)
      = −∂_(S\{g}) X(A\{g}) + ∂_(S\{g}) X(C0\{g}).

Indeed, with g retained, applying any of the other corner differences to
the f-relative identity preserves its witness g,bz. The displayed residual
is exactly the part with g deleted. Its states lie in the smaller diagram
D\{g}, but its signed multiplicities must still be regrouped into ENTIRE
components before smaller-area induction can cancel it.

## Why the arbitrary deletion quotient is ordinary

A circular corner deletion can admit new normal selections that were cyclic
before deletion. Its whole target component may therefore escape the image
of a source component. The following diagnostic uses zero-based vertices:

    D:    area (1,2,2), strict {02,21}, normals {01,12,20};
    D\21: area (1,1,2), strict {02},    normals {01,12,20}.

The selected relation {02,21,01} is acyclic and forms a singleton source
component. After deleting 21, its image belongs to the two-state component

    {02,01}  ↔  {02,12},

supported by the long 02. Reinserting 21 into the right-hand state creates
the cycle 1→2→1, so it is not an admissible source state. Thus even this
single deletion fails the ordinary spanning-subgraph reconstruction.
The source singleton itself is a chain and satisfies the HRV formula;
this is a counterexample to the proposed circular graph map, not the theorem.

Primary checked the lifted covers by hand and with the existing circular
model. The external receipt is
`component-recurrence/circular_corner_deletion_escape.json` under
`/lake-cache/ai-projects/requests/VerticalStripLLT/`, SHA-256
`80ec26168d5545469b710c3fbbe8f6c5e12ffcdd929c8adaa65c69f7dacb86b1`.
No new enumerator, Rust edit or build was used.

The alternating STATE cancellation still holds if the redundant circular
corner has an alternate path to its exact endpoint lift: that path cannot
use another maximal strict interval. What fails is the unrestricted global
regrouping into whole deletion components. The earlier
[always-redundant-corner lemma](FLIP_COMPONENT_INDUCTION.md#general-reduction-an-always-redundant-strict-corner)
justifies reinsertion along a particular component and remains valid in the
circular setting. The general primitive circular case remains open.

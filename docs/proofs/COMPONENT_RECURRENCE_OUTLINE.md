# Component e-positivity by recurrence

Working proof outline, 2026-09-29. We follow the author's construction:
push one complete component through a recurrence, repair the resulting
pieces by local diamonds, and collect whole components in smaller diagrams.
The general reassembly lemma remains to be proved. The component theorem
itself is already known by the separate word proof; that theorem is not an
input to this proposed recurrence proof.

## 1. The identity that gives positivity

We work first with an ordinary decorated natural graph on ordered vertices
0,...,n-1. A state A is its selected forward relation, including all strict
corners. Actual flips exchange the two normal shorts of a natural triangle
while retaining its selected long edge, with the required reachability
covers. Let C be one complete flip component.

For a fixed finite alphabet, let K(A) be the enumerator of colorings strictly
increasing along all selected edges. Let lambda(A) be the partition of n
formed by the fibre sizes of the highest-reachable-vertex map, including
isolated vertices. We aim to prove

    K(C) = E(C),
    K(C) = sum_(A in C) K(A),
    E(C) = sum_(A in C) e_(lambda(A)).                 (1)

This proves symmetry and e-positivity together: the coefficient of e_lambda
is the number of states in C with HRV partition lambda. It is enough to
establish (1) for every finite alphabet; these identities give the stable
symmetric-function identity in degree n.

Every flip exchanges one selected normal edge for another. Thus the normal
ascent number k(C) is constant on C. Restoring the shifted LLT parameter t
gives t^k(C) E(C), with coefficients in the nonnegative integers in t.
We prove the unweighted identity first, so marking and unmarking corners
do not obscure the component maps with different local powers of t.

## 2. Reductions that already preserve whole components

We can use three reductions before the chosen recurrence.

**An unmarked natural corner.** Its selected status is constant on C:
it cannot be a short edge of a natural triangle. If absent, delete it; if
selected, mark it strict. In either case the entire flip graph on that
stratum is unchanged, with all exterior edges present. This is the identity
map in the [notebook source map](COMPONENT_NOTEBOOK_MAP.md).

**A redundant strict corner.** If a strict corner is redundant at every
state of C, delete it. The established inactive-corner lemma identifies C
with a whole component in the smaller diagram, preserving K and E.
Redundancy at a single state is insufficient.

**The selected-edge envelope.** Take all natural intervals contained in a
selected edge of any one state in C. A flip preserves this envelope, since
both exchanged shorts lie inside its retained selected long. Delete natural
corners outside it and mark every remaining maximal edge strict. The corner
maps give a saturated diagram representing exactly the same component.
The selected relations, K and E are unchanged.

We use these reductions on each whole output component as well. A recurrence
may produce unmarked corners; it need not preserve saturation. The reduction
proofs are in [corner branching and envelopes](FLIP_COMPONENT_INDUCTION.md)
and [the notebook map](COMPONENT_NOTEBOOK_MAP.md). No cycle-rank classification
is required for this outline.

## 3. What it means to push a component through a recurrence

Start with the actual members of C. Split them according to the displayed
local arrows of the recurrence, keeping every exterior arrow. Apply the
same local identity to the coloring and HRV expressions. Three kinds of
maps recur in the diagrams:

- An identity map keeps the selected relation and may change which maximal
  edge is marked strict.
- A row/column interchange relabels the entire selected relation. For the
  adjacent interchange used here, an outgoing distinguished edge ensures
  that the two vertices are not both sinks; their swap preserves sink order
  and hence the HRV fibre sizes as well as the coloring enumerator.
- A diamond replaces a sum of two local states by another sum of two states.
  We use the same four terms for K and E, without requiring a pointwise
  bijection between the two middle states.

These operations give pieces in the output diagrams. To finish the step,
every orientation of an output component must occur with the same signed
multiplicity. We check this along every actual output flip, including flips
whose third vertex lies outside the displayed recurrence.

For a bijective piece, checking forward and inverse flip transport identifies
its whole component. For signed pieces, the local diamonds can redistribute
missing or excess orientations between several output components. Each
correction must preserve both valuation identities and close all boundaries
it changes. The notebook's red component brackets indicate exactly this
reassembly step.

One useful repair adds a complete source component I that can be deleted to
a smaller diagram, carries C+I through the recurrence, and subtracts I in
that smaller diagram. The proved five- and six-vertex DN constructions use
this operation. We may use more than the two initial output diagrams.

## 4. The precise remaining component lemma

**Required push-through lemma.** For every component not already reduced
to a terminal case, choose an eligible recurrence and perform the preceding
local operations to obtain

    X_D(C) = sum_i m_i X_(D_i)(C_i),       X=K,E,       (2)

where every C_i is a complete component in a strictly smaller diagram,
and the same integers m_i occur in both identities.

A construction using source additions should exhibit them explicitly:

    X_D(C) + sum_j a_j X_D(I_j)
      = sum_i b_i X_(D_i)(C_i),         X=K,E.

Each whole I_j must have an independently proved identification with a
whole component of a smaller diagram. Subtracting these identifications
then gives (2). Adding other unsolved components and knowing only their
combined sum does not isolate C.

The coefficients m_i may be negative. Induction applies to the equality
K=E, so the same signed correction disappears from their difference:

    K_D(C)-E_D(C)
      = sum_i m_i (K_(D_i)(C_i)-E_(D_i)(C_i)) = 0.     (3)

Positivity follows from the original definition of E(C), whose summands
are elementary functions with coefficient one. We therefore need no
positivity assertion for the intermediate signed recurrence.

The implication (2) => (1) is proved by this induction argument. Producing
(2) uniformly, including the component-boundary checks, is the open step.

There is now an exact partial completion of this step for DN. The
[homogeneous completion theorem](COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image)
determines the smallest union U_k(C) of k-edge source components containing
C whose unmodified direct image is a sum of whole output components.
Three explicit kinds of pairwise coefficient equalities generate this
union. Its indicator gives an identity for both K and E with output
coefficients in {-1,0,1}. No local exterior flip is omitted from its
closure proof. What remains for this construction is to reduce every
extra member of U_k(C) independently, so we can subtract it and isolate C.
That reducibility statement is not yet proved. If it fails for the known
reductions, joint output diamonds or other allowed recurrences remain
available; homogeneous closure is a sufficient route, not a restriction
on all possible proofs.

The [NN companion](COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer)
proves the same minimal-union statement for the initial NN split. Its
classes V_k(C) use the two r-selected output sizes and the r-absent
q-exit equations. Thus both recurrence types now have complete output
reassembly for explicit forced source unions. A sufficient remaining
theorem for this route is independent reducibility of every extra member
of U_k(C) or V_k(C) at the first-drop contacts. Together with DD/ND
inheritance and the proved induction coverage, that statement would finish
the ordinary component expansion. It remains unproved.

We must distinguish a local source-path repair from this coefficient
reassembly. In a first-drop DD intermediate, the upper natural corner h
is unmarked and its selected status is invariant on source components.
The new target corner can retain a flip that exchanges h. Its two source
preimages have opposite h-status, so a universal source-path repair is
impossible. The [forced-addition analysis](COMPONENT_DN_SOURCE_ADDITIONS.md#the-unmarked-upper-corner-forces-source-additions)
gives the explicit 01222 example, its complete recurrence, and the exact
compatibility equations for adding h-absent components. Every such added
component deletes to D-h. This boundary requires coefficient correction;
it is not a further missing cover case in a universal connectivity lemma.

The notebook's initial decomposition is now reconstructed exactly. Its
identity sectors already give whole components. Its remaining sector uses
reverse DN; equation (N2) in the [notebook note](COMPONENT_NOTEBOOK_MAP.md)
gives a valid split for one such component, with an explicit deletion
residual. The direct DN note gives the opposite direction. Neither initial
split has yet been collected into whole components in arbitrary exterior.

## 5. A complete example of splitting, repairing and collecting

Take the complete natural graph on four vertices with strict corner 03.
Write a=01, b=02, c=12, d=13, e=23, f=03. The five states

    C = {fabc, fabd, fbcd, fbde, fcde}

form a complete component. Delete f. In the smaller diagram the following
sets are complete components:

    D1={abd,bcd,bde},        D2={abcd,abde,bcde},
    D3={be},                D4={abe,bce}.

First use the diamond retaining f, followed by the empty/full endpoint
maps. The direct image of C is

    X(C) = X(D1) + [abcd] + [bde],       X=K,E.

Here brackets denote a single-state valuation. The last two terms are
incomplete pieces. Two diamonds retaining b, together with deletion of d
when it is redundant through c,e, give

    [bde] = [abde]+[bcde]+[be]-[abe]-[bce].

The pieces now collect into whole components:

    X(C) = X(D1)+X(D2)+X(D3)-X(D4),      X=K,E.         (4)

The construction and all component checks are in
[the direct NN example](COMPONENT_NN_REDISTRIBUTION.md). It is a complete
instance of the required step, including its negative correction.

To see the positivity at the end, the five HRV partitions in the displayed
order of C are (2,2), (3,1), (3,1), (4), (4). Consequently (4), together
with the smaller-component identities, gives

    K(C) = e_(2,2) + 2 e_(3,1) + 2 e_(4).

All five states have three selected normal edges, so the weighted
component contribution is t^3 times this expression. The sign in (4)
does not become a negative elementary coefficient in the final formula.

## 6. Induction order and the other recurrences

For a saturated envelope with ordinary area entries a_j, use the order

    (n, A, M),       A=sum_j a_j,       M=sum_j j a_j,  (5)

ordered lexicographically. The measures are nonnegative integers. Corner
deletion and the direct NN target decrease A. Direct DN replaces the natural
edge wz by ux, where x<z, preserving A and decreasing M by z-x. The resolved
ordinary DD target has the same area-entry change. Normalizing an output
component's envelope either decreases A further or merely marks corners,
leaving (A,M) unchanged. These decreases are proved in
[the ordinary DD measure](COMPONENT_DD_PACKETS.md).

This is an order for the FORWARD DN direction. The notebook's top row
is instead F(D0)=t F(I)+F(II)+t F(III), with reverse DN in the
selected-corner sector. The top row decreases doubled decorated area,
but after marking that selected corner, reverse DN preserves area and
increases M. We cannot mix it with forward neutral DN steps and claim
that (5) decreases. The [direction calculation](COMPONENT_NOTEBOOK_MAP.md#direction-and-the-induction-order)
records the exact changes. We now fix the forward direction and use the
first-drop coverage argument below. The notebook remains the source for
the split/repair/collection method; its reverse move is not mixed into (5).

Marking a corner is a representation change, not a recursive call on an
equally large unknown problem. We also do not invoke induction on an unmarked
intermediate merely because it occurs while deriving a DD or ND relation.
Only the final whole components on the right of (2) may use induction.

For the terminal natural diagrams that are disjoint chains, no triangle
supports a flip. Every component is a singleton and its selected relation
is a disjoint union of chains. A chain with ell vertices contributes e_ell,
so (1) is immediate by multiplication, including isolated vertices.

The [first-drop coverage theorem](COMPONENT_RECURRENCE_COVERAGE.md) supplies
a complete choice compatible with (5). For a connected saturated natural
diagram that is not a path, append a_n=0 and choose the first t with
a_(t+1)<a_t. Then a_t>=2. Put x=t-a_t and y=x+1<t. All entries through
a_t are nondecreasing, so a_y is a_x or a_x+1. The former gives DN or DD;
the latter gives NN or ND, according to the strict status of row y.
The proof checks the full local hypotheses, including the root gap and
the extra ND/DN area bounds. In particular area 012333 has an ND contact
at root 25, so it is covered.

The [one-component inheritance argument](COMPONENT_DD_PACKETS.md#direct-one-component-inheritance-for-dd-and-nd)
reduces DD to DN and ND to NN by unmarking the obstructing corner.
The selected-corner sector is exactly the same whole component, and the
final NN/DN outputs decrease (5). Thus general NN/DN reassembly suffices
for all four types. More precisely, it is enough to prove reassembly at
these first-drop contacts, for saturated sources or their intermediates
with just the upper contact corner unmarked and selected by C.
No component theorem is assumed in the equal-measure unmarked intermediate.
The coverage note gives the resulting conditional induction, including
natural-component factorization and the chain base case. Coverage and
well-foundedness are proved; general whole-component reassembly remains.
This outline concerns ordinary components. A circular extension requires a
separate order or reduction for recurrences crossing the chosen cut.

## 7. Where the supporting pieces fit

| Task in the outline | Main source | Proven scope / remaining work |
| --- | --- | --- |
| Author's diagrams and identity maps | [Notebook map](COMPONENT_NOTEBOOK_MAP.md) | Top row reconstructed; identity sectors and reverse initial split proved; general DN collection remains |
| Whole-component normalization | [Corner branching and envelopes](FLIP_COMPONENT_INDUCTION.md) | Proved; read the reduction sections, not the later optional matrix formalism |
| One-component NN split and repair | [NN redistribution](COMPONENT_NN_REDISTRIBUTION.md) | General initial split; full worked example |
| Larger complete NN step | [NN left reassembly](COMPONENT_NN_LEFT_REASSEMBLY.md) | Saturated eligible connected unicyclic case; arbitrary cycle rank remains |
| Middle-state transfer at exposure | [General exposure](COMPONENT_CORNER_EXPOSURE.md) | Both left/right exposing exits, with arbitrary exterior and cycle rank; intervening q-free paths remain |
| Transfer between covering anchors | [Two-anchor transfer](COMPONENT_RIGHT_ARM_TRANSFER.md#arbitrary-exterior-transfer-with-two-covering-anchors) | Arbitrary exterior for covering arms and the stated outgoing-cut extension; a general shared-branch repair remains |
| Incoming-arm transfer and left DN overlap | [Shared-branch repair](COMPONENT_INCOMING_EDGE_TRANSFER.md#closing-the-shared-covering-branch) | Arbitrary exterior with uw,td,ut covering and at least one outer anchor covering; both redundant outer anchors and other cover failures remain |
| One-component DN split | [Direct DN overlaps](COMPONENT_DN_DIRECT_OVERLAPS.md) | General identity; two ordered five-vertex overlap types remain |
| DN diamonds and minimal components | [Joint repairs](COMPONENT_DN_JOINT_REPAIRS.md) | Both minimal pictures completed; local propagation lemmas |
| Additional whole source components | [Source additions](COMPONENT_DN_SOURCE_ADDITIONS.md) | Six-vertex example proved; general construction remains |
| Exact completion at fixed selected-edge count | [Homogeneous DN completion](COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image) | Smallest required source union and complete output proved; independent reduction of every extra source component remains |
| The corresponding NN completion | [Homogeneous NN completion](COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer) | Same minimal-union theorem; the five-state example adds one whole inactive two-state component |
| DD boundary exchanging the upper corner | [Forced deletable additions](COMPONENT_DN_SOURCE_ADDITIONS.md#the-unmarked-upper-corner-forces-source-additions) | Exact arbitrary-exterior equations and all-sector reduction proved; compatibility between forced additions remains |
| Retained-edge source paths | [Retained-edge repairs](COMPONENT_DN_RETAINED_EDGE.md) | Arbitrary-exterior conditions, selected suffixes and an incoming-cut preparation with multiple obstructions; unrestricted case remains |
| Moving only the distinguished short | [Crossing-cover paths](COMPONENT_DN_RETAINED_EDGE.md#sliding-the-moving-edge-along-crossing-covers) | An arbitrary-length alternating path proves the retained-edge comparison, allowing both anchors redundant; path existence remains a hypothesis |
| DD/ND inheritance | [Corner-unmarking reductions](COMPONENT_DD_PACKETS.md) | DD reduces to DN, ND to NN, keeping the same whole component |
| Recurrence choice and induction | [First-drop coverage](COMPONENT_RECURRENCE_COVERAGE.md) | Proved for every ordinary saturated diagram; NN/DN reassembly is the remaining induction input |

The older [detailed catalogue](../COMPONENT_NOTE_CATALOGUE.md) retains the
supporting NN tree/bridge arguments, further examples and previous approaches.
They are available tools, rather than extra hypotheses imposed on the main
component push-through lemma.

## 8. Next proof work

The notebook's I/II/III cells and positive signs have been reconstructed,
and its two identity sectors are resolved at the component level. The
middle states must be paired by a diamond: the proposed individual poset
map fails already on four vertices. The smallest component calculation
is now written out completely in the notebook note.

For arbitrary exterior, follow one of the exact initial DN splits to the
first flip crossing a red component bracket and give the matching repair.
Fix the recurrence direction before invoking the induction order; switching
between the forward note and reverse notebook move is not a decrease.

For DN the direct-overlap analysis already locates the unsettled comparisons.
The general exposure lemma now removes cycle-rank assumptions from the
left/right exits which make the retained corner cover. Consequently a
nonzero unmatched middle coefficient cannot reach exposure while keeping
the adjacent short selected until the last step. The next middle-state
problem is an intervening path on which that short is absent and the corner
remains redundant. This is separate from the left retained-e-prime overlap.
The retained-deleted-edge and left retained-e-prime cases are the next local
checks; the target and corner-deletion pieces must be repaired together.
The two-anchor transfer now handles arbitrary-exterior covering arms and
clears a DN incoming cut when its obstructing branches have no selected
direct wv. A selected direct common branch remains outside that preparation.
Keep this precise obstruction separate from the already-resolved exposing
exit and from an assertion that all redundant-arm transfers are proved.
The left comparison now has a complete arbitrary-exterior repair when
uw,td,ut cover and at least one outer anchor wz,xz covers (with the stated
absent shorts and t not reaching x). First expose the other outer anchor.
Transfer the nonshared proper w-arms to x; if a shared branch remains,
expose its two covering arms, borrow tv along its suffix, and use the
proved delayed restoration. A second outgoing cut permits that inverse
with arbitrary competing x-branches. Both direct arms wd,xd may start
redundant. The separate four-flip row also handles covering wd,xd with
both outer anchors redundant. A saturated genuine first-drop DN diagram
supplies td as a strict edge, but not its cover. The remaining cover
failures, especially both redundant outer anchors and redundant td, need
further repair or source additions; shared paths under the proved cover
hypotheses are no longer an extra gap.
For the DD intermediate, do not demand source paths across the boundary
exchanging its unmarked upper corner: opposite corner statuses forbid them.
Use the proved forced-addition equations there and establish compatibility
with the other left comparisons, q-changing flips and deletion terms.
For the unmodified direct DN split at fixed selected-edge count, closure
is now exact for the forced union U_k(C). Use the local paths to identify
its paired representatives within actual source components, and the known
corner maps to reduce genuinely added components. The outstanding global
claim is that every extra component so forced can be independently
reduced; no such general claim is yet proved. Joint diamond corrections
may be needed if this source-addition construction cannot isolate C.
The NN companion gives the same conclusion for V_k(C), with the same
unproved independent-reduction requirement for its extra members.
The first-drop theorem now gives a
compatible choice for every ordinary diagram, and DD/ND inheritance supplies
their component steps from NN/DN. It is enough to settle transport at those
first-drop contacts and the stated selected-corner intermediates. The
remaining obligations are the general transport and collection statements;
coverage is no longer an additional gap.

The latest crossing-cover lemma supplies a direct retained-edge repair when
the moving short can slide along selected covers crossing its middle vertex.
It also identifies exactly when a path is possible while every background
edge stays fixed. If it fails, use a preparation that changes background
edges or a joint diamond correction. Do not replace this task by a general
single-arm transfer: the [five-vertex obstruction](COMPONENT_RIGHT_ARM_TRANSFER.md#why-absence-of-a-target-path-does-not-replace-the-anchor-covers)
proves that transfer false, even with no path from the receiving root to
the arm endpoint and even when the starting component is active at its
strict corner. The original retained-edge comparison has extra data and
has not been refuted by that example.

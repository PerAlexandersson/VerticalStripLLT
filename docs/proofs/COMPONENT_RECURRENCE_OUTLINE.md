# Component e-positivity by recurrence

Working proof outline, 2026-09-29. We follow the author's construction:
push one complete component through a recurrence, repair the resulting
pieces by local diamonds, and collect whole components in smaller diagrams.
The user prioritizes the recursion of whole components; the coloring identity
then follows from the same local maps. The general reassembly lemma remains
to be proved. The component theorem
itself is already known by the separate word proof; that theorem is not an
input to this proposed recurrence proof.

The current task is the direct image of ONE left-hand component under each
of the four recurrences, allowing further diamonds and vertex relabeling
on the right. The source-union criteria below are sufficient constructions,
not extra requirements of that task. A shorter
[NN repair entirely in its RHS diagram](COMPONENT_NN_REDISTRIBUTION.md#a-shorter-repair-entirely-in-the-nn-right-hand-diagram)
now gives the worked example with three target components and no source additions.

The new [residual-elimination lemma](COMPONENT_NN_REDISTRIBUTION.md#eliminating-every-unmatched-term-into-the-actual-rhs)
moves every unmatched NN or DN term into its actual RHS with at most one
extra diamond, retaining arbitrary exterior edges. The left DN four-state
component also has a direct [RHS-only repair](COMPONENT_DN_JOINT_REPAIRS.md#a-direct-rhs-only-repair-for-the-left-four-state-component).
All 210 source components in six fixed diagrams collect into integral RHS
component combinations when sink-order-preserving poset relabelings are
allowed. This finite evidence does not settle uniform collection; the
new residual replacements can change other output flip boundaries.

The [prepared-swap continuation](COMPONENT_NN_REDISTRIBUTION.md#prepared-adjacent-swaps-and-their-component-boundaries)
now proves an induced-sector graph isomorphism for NN and two analogous
DN channels. Corrections taken on entire induced components preserve
internal flip comparisons; only insertion of the distinguished short or
loss of a required bypass can change a boundary comparison. The seven
five-vertex NN repairs need just one prepared contact-swap relation.
The outstanding construction must cancel the remaining sector exits;
induced-sector components are not automatically whole target components.

The [boundary-descent identities](COMPONENT_NN_REDISTRIBUTION.md#descending-the-prepared-swap-boundary-identities)
now cover both exit types for NN and both prepared DN channels. Paired actual
flips and diamonds give successor pairs with fewer edges, or the same edge
count and greater reachability. A strict retained e' is deleted in the smaller
DN diagram R-e'. Every permitted step decreases an explicit measure, but
successor pairs need not remain in the proved class. Coupled collection of
those successors into whole components is still required. The first-drop
012333 example also rules out cancelling exits by a universal exposed-source
swap membership assertion.

The user has explicitly redirected us to the notebook's diagram reasoning:
keep one source component, pair the middle configurations in the diamond,
use the endpoint maps, and supply the missing members of whole RHS
components. Basis calculations are not part of this proof. The latest
[paired-flip lemma](COMPONENT_NN_REDISTRIBUTION.md#following-the-swap-through-a-further-flip)
lets us follow the swap after a bypass is lost, but does not close the
q-insertion and retained-corner boundaries. Keep the resulting signed
terms together when finishing those component brackets.

The [no-joint-selection lemma](COMPONENT_NN_REDISTRIBUTION.md#pairing-the-middle-states-when-joint-selection-is-absent)
now proves one middle comparison with arbitrary exterior. If a component
never selects q,r jointly, every r-selected state has both displayed
arms as bridges and flips directly to its same-exterior q-selected mate.
Otherwise a corner-deletion preparation and explicit path would introduce
q while keeping r. Thus its initial NN image has zero-or-one coefficients.
This does not finish collection: the note gives an actual target flip
whose endpoints have coefficients zero and one in an unsaturated example.
The corresponding DN middle residual is nonnegative, but its remaining
coefficients and whole-component collection still need repair.

The [full-layer tree recurrence](COMPONENT_NN_REDISTRIBUTION.md#full-layer-recurrence-for-arbitrary-source-trees)
now resolves these issues for arbitrary source tree components, including
unsaturated ones. Complete the n-1-edge source layer and subtract every
extra component: a connected extra is a tree with smaller envelope;
a disconnected extra becomes one whole smaller component by reordering
its induced weak blocks. This gives NN target layers n-1 and n-2,
or just layer n-1 for DN, minus independently smaller corrections.
The eleven-state raw-image boundary above has a complete recurrence
by this construction. The remaining full-layer isolation problem is
cyclic: several connected full-envelope components can have the same
edge count. No general uniqueness or reduction of all extras is proved.

The [dense-corner theorem](COMPONENT_NN_REDISTRIBUTION.md#the-largest-edge-layer-in-which-a-corner-can-cover)
now isolates one cyclic class uniformly. For a strict corner f of length
d in a graph with N natural edges, k*=N-d+1 is the largest possible
edge count with f covering. At equality, all covering states are cut
states joined by actual f-retained flips. Hence there is exactly one
f-active component in that layer, and every other source-layer component
independently deletes f. The full NN/DN layer identities therefore give
complete signed recurrences, with exact whole-component cancellations
in NN. All components above the layer delete f as well. This includes
complete-graph components of unbounded cycle rank. General lower cyclic
layers, with additional missing edges, remain outside the cut proof.

The [simultaneous-corner theorem](COMPONENT_NN_REDISTRIBUTION.md#the-largest-layer-with-all-corners-covering-simultaneously)
now gives a sharper maximum layer using ALL maximal natural corners.
The pairs ab,bc belonging to a corner ac form disjoint paths on the
nonmaximal edges. If their lengths are l_j and the corners are M, put
m*=|M|+sum ceil(l_j/2). This is the largest edge count with all M covering
simultaneously. At equality, a rightmost-corner actual-flip normalization
connects every such state to one alternating selection. Exactly one whole
component survives; every other component either deletes an absent corner
or reduces by alternating corner deletion. Full NN/DN layer identities
therefore give complete signed recurrences at m*. Every higher layer
also reduces. This handles arbitrary crossing exterior and unmarked
corners, including the 77-state NN component at k=9 in 012333 and the
2305-state component at k=12 in 0123434. Lower layers remain open: the
priority argument requires maximum selections on the auxiliary paths.

The [lower-layer obstruction and preparation](COMPONENT_NN_REDISTRIBUTION.md#lower-layers-require-temporary-redundant-corners)
show that temporary redundant corners are essential. An all-cover state
in area 012333 has no all-cover neighbor, yet six corner-retaining flips
connect it to another all-cover state. We now normalize ANY all-cover
state along entire corner chains: process one chain until it is absorbing,
then all other corners recover their covers. This proves an actual path to
the explicit chain-max anchor even from an initially mixed-cyclic state.
It does not connect all anchors in a component or collect their recurrence.
The two states of the obstruction are already anchors.

The [cube-family theorem](COMPONENT_NN_REDISTRIBUTION.md#complete-component-recurrences-for-cubes-of-paths-on-3h-vertices)
now completes NN/DN component recurrences in EVERY edge layer for the
natural cube of a path on 3h vertices. After corner-chain normalization,
anchors are subsets of h disjoint triangles. Explicit six-vertex moves
rearrange each edge type and change two-edge triangle selections; the
resulting row/count argument connects all anchors with the same edge
count and weak-component partition for arbitrary h. Thus every connected
source layer has one simultaneous-cover component; all extras independently
reduce by missing corners, weak blocks or alternating corner deletion.
This solves the former 125-state case in area 012333. The different chain
geometry of area 0123434 is now covered by the finite certificate below.
No arbitrary-diagram anchor-connectivity theorem is asserted.

The [outer-cover triangle exchange](COMPONENT_NN_REDISTRIBUTION.md#triangle-exchange-with-a-covering-outer-edge)
has an exact three-cover criterion with arbitrary ordinary exterior; its
retained outer edge may be normal. The companion
[unequal-chain certificate](COMPONENT_NN_REDISTRIBUTION.md#a-checked-whole-component-recurrence-with-unequal-chains)
now completes every NN layer of area 0123434 with 04,26 strict, including
its 3381-state component. Independently replayed trees connect all 674 connected anchors
in the seven relevant layers, and every other source component has a
whole smaller block/deletion expression. This is a finite certificate
for that diagram. The local generators still have gaps in other diagrams;
they are not a proved general description of component connectivity.

The new [empty-corner reduction](COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram)
shows that the uniform NN statement would also settle DN. Adding the
missing corner EMPTY and unmarking its neighbor preserves the exact
source component and makes NN eligible. Whole NN outputs then split by
identity into the DN target and smaller deletion diagrams. This is a
proved conditional reduction, not completed NN/DN collection. The NN
statement must allow the empty unmarked corner and the eligible contact;
the enlarged source need not be saturated or have its first drop there.

A new [whole-component certificate](COMPONENT_NN_REDISTRIBUTION.md#a-complete-component-certificate-beyond-cycle-rank-one)
handles an 84-state connected NN example by completing its source brackets,
deleting twelve inactive additions and cancelling eight whole terms. It
uses diagrams and actual component checks only. The
[one-end attachment theorem](COMPONENT_NN_REDISTRIBUTION.md#nn-recurrences-extend-at-the-fixed-right-endpoint)
extends it to arbitrary components attached on the right, where the NN
swap fixes the shared endpoint. These results do not close arbitrary
crossing exteriors or the general empty-corner NN source.

The [two-recurrence example](COMPONENT_NN_REDISTRIBUTION.md#using-dn-to-separate-two-surviving-nn-components)
now resolves an empty-corner case where same-layer completion forces two
surviving source components. A DN full-layer calculation minus one matched
singleton handles the 69-state component; substituting it into their NN
component union handles the 126-state component. Both identities extend
to arbitrary endpoint attachments on both sides. This is a direct diagram
certificate for that case, not a general assertion about forced additions.

The [fixed-short theorem](COMPONENT_NN_REDISTRIBUTION.md#components-on-which-the-adjacent-short-is-fixed)
now handles every NN component on which q=wx has constant selected status,
with arbitrary exterior. A leftward cover-flip descent excludes an entire
01 component; sector 00 maps by the endpoint swap to a whole target
component, and sectors 10 and 11 use redundant-corner deletion. The
[DN consequence](COMPONENT_DN_JOINT_REPAIRS.md#dn-components-on-which-the-adjacent-short-is-fixed)
gives the corresponding three whole-component maps and decreases the
original DN induction order. The general case where q varies remains open;
the new descent does not prove general middle-state connectivity.

Some variable-q components are now reduced by the
[fixed terminal-short theorem](COMPONENT_NN_REDISTRIBUTION.md#when-the-terminal-short-is-fixed).
If r is always selected, a cover-preserving cut proves that f is
everywhere redundant, so corner deletion gives one whole smaller
component. The [general absent-r continuation](COMPONENT_NN_REDISTRIBUTION.md#removing-the-least-vertex-restriction)
now removes its earlier least-vertex restriction, including incoming DN
edges. It uses Hasse-path shortening and two block cases after making
f the sole outgoing edge at w. Thus ALL fixed-r components are reduced
for NN and DN. General collection remains open when BOTH short edges
vary; the new paths do not establish same-exterior middle membership
or the required whole-component multiplicities in that case.

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

The [shorter RHS repair](COMPONENT_NN_REDISTRIBUTION.md#a-shorter-repair-entirely-in-the-nn-right-hand-diagram)
replaces D3-D4 by the negative singleton component T={acde}. Thus the
same example is X(C)=X(D1)+X(D2)-X(T), entirely in the shortened NN
diagram with strict edge d. One additional diamond suffices after the
initial split; all three RHS components are checked directly.

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
| Covers at either left endpoint | [Three-cover defect support](COMPONENT_DN_DIRECT_OVERLAPS.md#left-defects-vanish-on-three-cover-witnesses) | At a genuine first-drop DN contact, a nonzero left defect forces a redundant member of uw,td,wz at each source endpoint; the three-corner alternating valuations vanish there |
| One-component DN split | [Direct DN overlaps](COMPONENT_DN_DIRECT_OVERLAPS.md) | General identity; two ordered five-vertex overlap types remain |
| DN diamonds and minimal components | [Joint repairs](COMPONENT_DN_JOINT_REPAIRS.md) | Both minimal pictures completed; local propagation lemmas |
| Additional whole source components | [Source additions](COMPONENT_DN_SOURCE_ADDITIONS.md) | Six-vertex example proved; general construction remains |
| Arbitrary components attached at two ends | [Endpoint-attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit) | Proved for recurrences with endpoint-preserving DN maps; all fourteen left five-vertex rows extend; crossing exterior reassembly remains open |
| Complete source layers with a unique selected-corner component | [Full-layer criterion and square paths](COMPONENT_DN_SOURCE_ADDITIONS.md#isolating-one-selected-corner-sector-by-a-full-layer) | All saturated squares of paths on n>=5 have explicit signed whole-component DN recurrences; general selected-sector uniqueness is not asserted |
| Exact completion at fixed selected-edge count | [Homogeneous DN completion](COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image) | Smallest required source union and complete output proved; independent reduction of every extra source component remains |
| The corresponding NN completion | [Homogeneous NN completion](COMPONENT_NN_REDISTRIBUTION.md#exact-completion-within-one-selected-edge-layer) | Same minimal-union theorem; the five-state example adds one whole inactive two-state component |
| DD boundary exchanging the upper corner | [Forced deletable additions](COMPONENT_DN_SOURCE_ADDITIONS.md#the-unmarked-upper-corner-forces-source-additions) | Exact arbitrary-exterior equations and all-sector reduction proved; compatibility between forced additions remains |
| Retained-edge source paths with a covering outer anchor | [General r-cover theorem](COMPONENT_DN_RETAINED_EDGE.md#every-comparison-with-r-covering) | Complete arbitrary-exterior repair when either f or r covers at Q+xs; the both-redundant case remains |
| Constructing the needed covering interval | [Common-ancestor preparation](COMPONENT_DN_RETAINED_EDGE.md#advancing-a-common-ancestor-and-completing-the-r-cover-case) | Increasing common ancestor gives a covering interval below t or a terminal at; temporary-tz restoration handles arbitrary routes toward s |
| A lower bypass with both anchors redundant | [Seven-flip rows](COMPONENT_DN_RETAINED_EDGE.md#a-lower-bypass-when-both-outer-anchors-are-redundant) | ws,wt,xa,az,sz,tz covering and either w not reaching a or wa covering suffice; r may remain redundant after xs deletion |
| Arbitrary lower prefixes | [Preparation inside ws](COMPONENT_DN_RETAINED_EDGE.md#preparing-an-arbitrary-lower-prefix-inside-ws) | ws,wt,xa,sz,tz covering, w reaching a and r covering after xs,xa deletion suffice, with absent/redundant wa and no az cover |
| Extending the short before the closing row | [Q+xs to Q+xt](COMPONENT_DN_RETAINED_EDGE.md#extending-xs-to-xt-along-an-arbitrary-lower-prefix) | wt covering and w reaching s suffice; with r covering in Q and sz,tz covering, this finishes the retained-edge repair even with ws absent/redundant |
| Covers before adding the moving arm | [Background-anchor transfer](COMPONENT_RIGHT_ARM_TRANSFER.md#covers-in-the-background-and-an-absent-direct-suffix) | uc,vc covering in Q, neither root reaching d and absent dc suffice, with arbitrary d-to-c paths; selected redundant dc remains |
| Absent tz with longer suffix paths | [Retained-edge corollary](COMPONENT_DN_RETAINED_EDGE.md#an-absent-tz-with-arbitrary-paths-from-t-to-z) | wt covering, w reaching s and r,sz covering in Q suffice when tz is absent; combined with (51), only selected redundant tz remains under these other assumptions |
| Shared first edges and arbitrary suffix paths | [Shared-suffix transfer](COMPONENT_RIGHT_ARM_TRANSFER.md#a-shared-first-edge-with-an-arbitrary-suffix) | A redundant arm transfers when every competing route from each root starts with its shared covering arm; suffix edges and paths may be redundant or multiple |
| Redundant tz with covering proper incoming edges | [Selected-suffix corollary](COMPONENT_DN_RETAINED_EDGE.md#a-redundant-tz-with-covering-proper-incoming-suffix-edges) | Under the previous wt, reachability and background-anchor assumptions, redundant tz is allowed when the other incoming edges reached from t cover; superseded on suffix scope by (54) |
| Arbitrary suffix behind two background covers | [General background-anchor transfer](COMPONENT_RIGHT_ARM_TRANSFER.md#background-anchor-transfer-with-an-arbitrary-suffix) | Q+ud~Q+vd whenever uc,vc cover in Q and neither root reaches d; no suffix restriction, including selected redundant dc and comparable incoming tails |
| Retained repair after short extension, all suffix cases | [Corollary (54)](COMPONENT_DN_RETAINED_EDGE.md#removing-every-suffix-restriction-after-short-extension) | wt covering in Q+xs, w reaching s and r,sz covering in Q suffice; earlier suffix gaps are closed, while failures of these remaining assumptions are open |
| Retained repair with three covers only | [Theorem (58)](COMPONENT_DN_RETAINED_EDGE.md#the-lower-reachability-hypothesis-is-no-longer-needed) | wt covering in Q+xs and r,sz covering in Q suffice, with no w-to-s or suffix assumption; any remaining defect fails at least one of these covers |
| Push through a prefix after removing its short | [Prefix-push lemma](COMPONENT_DN_RETAINED_EDGE.md#pushing-a-short-along-a-prefix-that-does-not-already-reach-s) | R+ys~R+st when wt covers, w reaches y<s, w does not reach s and s does not reach t; all prefix edges are restored |
| Redundant containing wt with a controlled outer bypass | [Suffix restoration behind an incoming cut](COMPONENT_DN_RETAINED_EDGE.md#a-redundant-containing-edge-when-every-outer-bypass-passes-through-t) | With r,sz covering, all w-to-z bypasses passing through t and all proper incoming wt-bypass tails above s, arbitrary wt/tz redundancy is allowed; other path patterns remain |
| Arbitrary containing bypasses through t | [Theorem (61)](COMPONENT_DN_RETAINED_EDGE.md#allowing-incoming-bypasses-below-s-as-well) | r,sz covering in Q and every w-to-z bypass passing through t suffice; no wt cover, incoming-tail or suffix restriction remains |
| Lower bypasses rejoining after t | [Theorem (64)](COMPONENT_DN_RETAINED_EDGE.md#allowing-lower-branches-to-rejoin-the-suffix-after-t) | With r,sz covering, every w-reachable proper incoming z-tail also t-reachable, and only the upper incoming t-tails required to reach z through t, outer bypasses avoiding t are allowed |
| Matched preparations with arbitrary upper bypasses | [Theorem (65)](COMPONENT_DN_RETAINED_EDGE.md#matching-two-suffix-preparations-removes-the-upper-tail-restriction) | r,sz covering and equality J=K of the incoming z-tails reached from w and t suffice; transfer all prepared s-arms to x and reverse the exactly matched target preparation; no upper-tail guard remains |
| Interleaving incoming t/z cuts | [Theorem (69)](COMPONENT_DN_RETAINED_EDGE.md#interleaving-the-two-incoming-cuts) | With r,sz covering, t reaching z, all J tails above s and J disjoint from H, incoming tails not reached from t are allowed; common forks and lower z-tails remain |
| Moving only the distinguished short | [Crossing-cover paths](COMPONENT_DN_RETAINED_EDGE.md#sliding-the-moving-edge-along-crossing-covers) | An arbitrary-length alternating path proves the retained-edge comparison, allowing both anchors redundant; path existence remains a hypothesis |
| DD/ND inheritance | [Corner-unmarking reductions](COMPONENT_DD_PACKETS.md) | DD reduces to DN, ND to NN, keeping the same whole component |
| Recurrence choice and induction | [First-drop coverage](COMPONENT_RECURRENCE_COVERAGE.md) | Proved for every ordinary saturated diagram; NN/DN reassembly is the remaining induction input |

The older [detailed catalogue](../COMPONENT_NOTE_CATALOGUE.md) retains the
supporting NN tree/bridge arguments, further examples and previous approaches.
They are available tools, rather than extra hypotheses imposed on the main
component push-through lemma.

## 8. Current proof work after the account switch

The replacement primary resumed the ordinary diagram argument from the
pushed account-swap checkpoint. Read the concise
[current handoff](../../HANDOFF.md) for ownership, verification and exact
checkpoint status. Earlier chronology remains in the
[outline archive](../archive/component-recurrence-outline-before-account-switch-20260929.md).

The central open statement is still section 4: isolate one original C in
an identity with whole smaller components. Both fixed-short cases, arbitrary
source trees, the largest one-corner-active layer, and now the largest
simultaneous-corner layer have complete recurrences. In the latter case,
actual flips prove uniqueness of the component that survives alternating
corner deletion. This supplies an independent reduction for EVERY extra
component before full-layer subtraction.

The [endpoint-attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit)
is proved for endpoint-preserving maps, including its stated two-end
extensions. It does not by itself handle arbitrary crossing exterior.
The new maximum-layer theorem does allow such exterior, but requires
maximum nonadjacent selections on the auxiliary short-edge paths.

Continue with connected cyclic full-envelope components below that maximum,
after applying weak-block, absent/inactive-corner and fixed-short reductions.
The 125-state case in area 012333 is solved by the cube-family theorem;
the 3381-state case in area 0123434 is solved by its independent anchor
certificate. General paths through redundant-corner states still need
repair or replacement by direct RHS redistribution. Do not assume general
active-component uniqueness or subtract unreduced extra source components. Direct RHS diamonds remain
an alternative to full-layer completion. The available retained-edge
lemmas and paired endpoint maps may be used for local comparisons, but
their outputs still have to collect into whole components.

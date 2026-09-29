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

Marking a corner is a representation change, not a recursive call on an
equally large unknown problem. We also do not invoke induction on an unmarked
intermediate merely because it occurs while deriving a DD or ND relation.
Only the final whole components on the right of (2) may use induction.

For the terminal natural diagrams that are disjoint chains, no triangle
supports a flip. Every component is a singleton and its selected relation
is a disjoint union of chains. A chain with ell vertices contributes e_ell,
so (1) is immediate by multiplication, including isolated vertices.

We still need a complete choice-of-recurrence argument compatible with (5)
and the reassembly lemma. The recorded saturated coverage analysis uses
NN, DN, DD and ND; NN/DN/DD alone miss the diagram of area 012333. The
componentwise ND step and its decreasing final targets must be included
explicitly. Aggregate recurrence coverage alone does not finish this step.
This outline concerns ordinary components. A circular extension requires a
separate order or reduction for recurrences crossing the chosen cut.

## 7. Where the supporting pieces fit

| Task in the outline | Main source | Proven scope / remaining work |
| --- | --- | --- |
| Author's diagrams and identity maps | [Notebook map](COMPONENT_NOTEBOOK_MAP.md) | Corner maps proved; exact I/II/III transcription remains |
| Whole-component normalization | [Corner branching and envelopes](FLIP_COMPONENT_INDUCTION.md) | Proved; read the reduction sections, not the later optional matrix formalism |
| One-component NN split and repair | [NN redistribution](COMPONENT_NN_REDISTRIBUTION.md) | General initial split; full worked example |
| Larger complete NN step | [NN left reassembly](COMPONENT_NN_LEFT_REASSEMBLY.md) | Saturated eligible connected unicyclic case; arbitrary cycle rank remains |
| One-component DN split | [Direct DN overlaps](COMPONENT_DN_DIRECT_OVERLAPS.md) | General identity; two ordered five-vertex overlap types remain |
| DN diamonds and minimal components | [Joint repairs](COMPONENT_DN_JOINT_REPAIRS.md) | Both minimal pictures completed; local propagation lemmas |
| Additional whole source components | [Source additions](COMPONENT_DN_SOURCE_ADDITIONS.md) | Six-vertex example proved; general construction remains |
| Retained-edge source paths | [Retained-edge repairs](COMPONENT_DN_RETAINED_EDGE.md) | Several arbitrary-exterior sufficient conditions; unrestricted case remains |
| DD and induction order | [DD packets](COMPONENT_DD_PACKETS.md) | Corner split, packet transport and measure proved; one-component reassembly remains |

The older [detailed catalogue](../COMPONENT_NOTE_CATALOGUE.md) retains the
supporting NN tree/bridge arguments, further examples and previous approaches.
They are available tools, rather than extra hypotheses imposed on the main
component push-through lemma.

## 8. Next proof work

We first label the cells in the notebook's I/II/III diagrams and write each
map beside the piece it transports. Resolve the identity-map sectors at the
component level. For the remaining pieces, check the first flip that crosses
one of the red component brackets and give the matching local repair.

For DN the direct-overlap analysis already locates the unsettled comparisons.
The retained-deleted-edge and left retained-e-prime cases are the next local
checks; the target and corner-deletion pieces must be repaired together.
After those repairs, prove closure of the complete collected components,
then incorporate the corresponding NN/DD/ND steps into the induction order.
The outline is complete as a logical plan; these general transport and
coverage assertions remain mathematical proof obligations.

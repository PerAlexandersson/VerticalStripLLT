# Whole-component corrections for an NN recurrence

2026-09-28. The general recurrence/diamond proof remains open. We prove
a criterion for inactive unicyclic corrections and record a complete
finite reconstruction for a larger ordinary example. Neither result
establishes uniform component isolation.

## A boundary defect between two trees

Take area (0,1,2,3,4,3,4), strict corners 04 and 26, and the NN step
at 2<3<6. Thus q=23, r=36 and σ exchanges 2 and 3. The corner-deletion
diagram has area (0,1,2,3,4,3,3) and strict set {04}.

Let C be the complete source component with least mask 1567. It has
1,693 states, each a connected unicyclic graph, and it contains a
mixed-acyclic state. We use the masks only to identify exact finite
certificates; edges themselves are listed below.

The canonical NN transport of the indicator of C has coefficients 0
and −1 at the following target neighbors:

    U = {01,02,03,04,25,56},
    V = {01,03,04,23,25,56}.

They are related by retaining 03 and exchanging 02 with 23. Both are
trees, so neither has a redundant edge. In particular, we cannot repair
every initial boundary defect by deleting a redundant edge at one of
its endpoints. This does not preclude repairs that first introduce edges,
apply other diamonds, or change a whole source component.

The corresponding source middle pair is

    L10 = {01,03,04,23,25,26,56},
    L01 = {01,03,04,25,26,36,56}.

The second state belongs to C; the first does not. Both initially have
26 redundant through 25,56. In C, the flip retaining 36 and replacing
56 by 35 exposes 26. Reversing the strict edges in the resulting state
gives an acyclic directed graph, so this component survives the already
proved mixed-cycle reduction.

## A whole source correction

The component I containing L10 has 89 states. Delete 26 from L10. Its
tree envelope has maximal intervals

    M = {04,25,56}.

By [tree connectivity](COMPONENT_TREE_CONNECTIVITY.md), the entire deletion
component consists of trees with this envelope. Every one contains the
path 2→5→6. Thus adding 26 gives a whole component in which 26 remains
redundant. The new forced-reachability theorem in that note shows this
is the exact criterion for an inactive extension of a tree component.
Writing T for this complete tree component, we have

    X(I) = X(T),       X=K,E.

The [NN packet construction](COMPONENT_RECURRENCE_REDUCTION.md) gives a
whole-component recurrence for every connected class of its source
completion graph. Exhaustive construction of that finite graph here
shows that the class containing C consists precisely of C and I.
Consequently its target is a union U_R of whole components of the NN
diagram R, with area (0,1,2,3,4,3,3) and strict set {04,36}, and

    X(C) = X(U_R) − X(T),       X=K,E.

This is an individual component recurrence in smaller-area diagrams.
The local identities give the same coefficients for K and E. The proof
of packet transport is uniform; identifying this particular packet is
an exhaustive finite certificate, not a proof of general isolation.

The union U_R consists of 26 whole components, with sizes

    140,16,520,16,3,3,225,10,604,73,4,2,2,
    17,22,11,16,5,2,1,1,8,11,65,3,2.

Their total is 1,782=1,693+89. The receipt lists a seed for each one
and verifies that deleting 26 from I gives exactly the complete
89-state tree component containing U.

## What the finite check establishes

There are 1,405 source components and 703 completion classes in this
diagram. Exactly six source components remain after removing disconnected
components, trees, and components whose every state is mixed-cyclic.
No completion class contains two of those six. We checked constancy
of the transported packet indicators across all 55,232 directed target
flips, simultaneously for all packets.

The other five packets have 15, 38, 74, 103 and 109 source components.
Their larger numbers of corrections show why a single local boundary
identity need not describe the whole reconstruction.

The open assertion is that suitable corrections always suffice, or,
for this particular packet method, that a completion class cannot connect
two distinct components surviving the known reductions. The tree
criterion classifies one family of solved corrections but does not
control paths through all the other solved components.

## Reproduction

Related Rust: external consumer `nn_component_transport.rs`, modes
`--audit-cover-boundaries` and `--audit-packets`, and
`tree_forced_reach.rs`. Frozen sources, Cargo manifest and lock, commands,
receipts and hashes are under

    /lake-cache/ai-projects/requests/VerticalStripLLT/global-reassembly/

The shared Rust revision is d53fb193af3c69adedbd9ec8592f87235d809ffa;
its maintained sources were not modified. We reuse its graph and exact
valuation APIs. The finite actual-flip enumerator remains an external
research consumer, with integration tracked by
`suggestions/flip-enumeration-api.md`.

In the corner-deletion diagram the mask edge order is

    01,02,03,04,12,13,14,23,24,25,34,35,36,45,46,56.

Insert 26 immediately after 25 for the source edge order. Hence the
displayed U,V have target masks 33295,33421, and I has source seed
67087. `packets_shield.jsonl` records the full completion classes;
`cover_boundary_shield.jsonl` records the boundary defect. The additional
six-vertex and three-corner receipts test the same boundary predicate,
without asserting any global reconstruction theorem.

# Endpoint attachments: unfinished component-recursion continuation

2026-09-29 account-switch handoff. **Candidate argument, not yet an
established recurrence theorem.** The user requested a pause before its
complete audit and fixed attached-component checks. No such checks have
been run. This note preserves the next mathematical step, not a claim
that the general component proof is complete.

The user's latest priority is the recursion of complete components.
Once that is established, the coloring recursion should be a short
consequence of the same local identities. Do not return by default to
an indefinitely growing list of conditional local flip paths.

## What the existing small components require

The existing five-vertex left recurrence has source area 01222 and target
01231. There are fourteen source components and fifteen target components.
A one-to-one correspondence between all individual components is therefore
impossible. Its already-proved recursion includes

    X(C_1)=X(D_8)-X(I_11),

where C_1 has four states, D_8 has eight and I_11 has four. The last term
is a whole component in the smaller corner-deletion diagram. See the
[complete left construction](COMPONENT_DN_JOINT_REPAIRS.md#a-complete-component-recurrence-for-the-left-hand-diagram).
This is the kind of signed component recursion to generalize.

A new bounded check compared component HRV-partition profiles, retaining
selected-edge count, using existing actual components and the maintained
Rust HRV API. In area 01222, nine profiles have unequal multiplicities
between source and target, confirming the obstruction above. In the fixed
six-vertex area 012233, all profiles match between the twenty-six source
and twenty-six target components. The latter is finite evidence only;
it supplies neither a component bijection nor a general recursion.

Receipts and frozen consumer:
`/lake-cache/ai-projects/requests/VerticalStripLLT/component-dn-matching-20260929/`.
Commands: `dn_joint_span --component-profiles --left-five` and the same
with `--left-six`. These enumerate only the fixed 32-state and 256-state
source/target diagrams. No coloring enumeration is used in this mode.

## Candidate extension to arbitrary components attached at the ends

Take a diagram on [a,c] with an established component recursion obtained
from DN endpoint maps, diamonds and redundant/absent-corner deletions.
Attach arbitrary ordinary diagrams on its left and right, sharing only
a or c with the middle diagram, and choose one complete component in
each attachment. There are no natural edges crossing between interiors.

The proposed conclusion is the SAME signed component recursion after
gluing each term to the two chosen attached components, provided the
middle proof fixes its two endpoint marks. Three checks are required.

1. **Whole components.** Every natural triangle lies in one block. A
   forward path cannot leave a block and return to affect a cover test.
   Thus the full flip graph is a Cartesian product of the three block
   graphs, and a product of complete components is complete. This is
   the structural gluing statement already recorded in the
   [endpoint note](COMPONENT_ENDPOINT_GLUING.md#gluing-at-an-extremal-shared-vertex).
2. **Endpoint-marked local identities.** Keep the colors at a,c fixed.
   Coloring diamonds hold pointwise in every coloring. Redundancy and
   identity maps preserve them. The DN bottom swap exchanges internal
   w,x, with a<=u<w<x<z<=c, hence fixes both endpoint marks. The full
   endpoint map preserves the selected closure.
3. **HRV and gluing.** Replace each HRV fibre by its increasing chain,
   retaining the colors at a,c. The HRV diamond should hold already as
   a multiset identity of full HRV maps: with the long ij selected,
   compare the old reachable maxima at the middle vertex and j. If
   the middle maximum is at least the j maximum, adding the right
   short is inert in both left-short sectors; otherwise adding the
   left short is inert in both right-short sectors. Audit this with
   the full exterior and predecessors. For the DN bottom swap, audit
   preservation of fibre sizes, endpoint membership and whether the
   two endpoints share a fibre, using the known preservation of sink
   order. These data determine the endpoint-marked chain enumerator.

At an extremal shared vertex, the incident HRV fibres merge by joining
one chain's maximum to the other chain's minimum. The fixed-color
coloring sums glue the same way, counting the shared vertex once.
Consequently endpoint-marked identities would give the two unmarked
identities for the attached complete components, without assuming any
component expansion for the attachments. The existing aggregate gluing
proof is useful for these combinatorics; its aggregate theorem alone
must NOT be applied to a fixed component.

The first intended application is the complete five-vertex left table,
whose DN swap exchanges 2,3 and fixes endpoints 0,4. An explicit bounded
check can attach the two-state triangle component at each end: the
four-state/eight-state/four-state row should become 16/32/16 states.
One source area is 012122212 (two endpoint triangles and the 01222
middle block). Check actual components and the HRV identity without a
large enumeration. This fixture and its proof have NOT been executed.

This would cover arbitrary endpoint attachments, not exterior edges
crossing into the middle block. Such crossing exteriors and the general
source-addition/reassembly lemma remain the main unresolved problem.
Also do not automatically extend the endpoint argument to NN: its
bottom swap can move a marked endpoint and needs a separate check.

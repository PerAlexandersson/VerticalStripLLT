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

## Endpoint-attachment theorem: completed audit

2026-09-29, resumed from checkpoint `2511182`. The preceding text is the
unchanged candidate recorded at the account switch. We now prove its
endpoint-attachment conclusion, with the endpoint-preservation hypothesis
made precise. We also verify all fourteen recurrences of the five-vertex
left diagram after attaching the two prescribed triangle components.
This is a mathematical proof and a fixed exact check, not a new Lean theorem
or a proof of general reassembly with crossing exterior edges.

### The marked quantities

Let A be a forward selected relation on the interval [a,c], with a<c.
Write h_A(v) for its highest reachable vertex, allowing a path of length
zero. Let F(A) be the chain forest which orders each fibre of h_A by
increasing vertex label. For colors alpha,beta in a fixed finite alphabet,
we put

    K_A[alpha,beta] = sum_(f strict on A; f(a)=alpha, f(c)=beta) x^f,
    E_A[alpha,beta] = K_F(A)[alpha,beta].                       (EA1)

We sum these quantities over states with their integer multiplicities.
Summing both marks gives K_A and e_lambda(A), respectively. For the
one-vertex interval we use a single mark, counted once; its two-mark
quantity vanishes unless the marks agree.

The marked E quantity is determined by the sizes of the two endpoint
fibres, whether they coincide, and the multiset of all remaining fibre
sizes. Indeed a is the minimum of its fibre and c is the maximum of its
fibre. If their fibres are distinct, their factors are

    x_alpha e_(p-1)(X_>alpha),    x_beta e_(q-1)(X_<beta).

If they coincide, the factor is zero unless alpha<beta, and otherwise is

    x_alpha x_beta e_(p-2)(X_(alpha,beta)).

Every other fibre contributes its usual elementary function. We call
these sizes and the coincidence flag the endpoint fibre data. No claim
of linear independence of these marked expressions is needed.

### Diamonds preserve full HRV maps

Let i<j<k. Fix a forward relation B containing ik and omitting ij,jk.
Set B_00=B, B_10=B+ij, B_01=B+jk and B_11=B+ij+jk. There are no cover
hypotheses, and B may contain arbitrary exterior edges and predecessors.
Then, as multisets of functions on the entire vertex set,

    {h_B10,h_B01} = {h_B00,h_B11}.                            (EA2)

To prove this, first observe that adding an edge uv cannot change any
HRV value when h_B(u)>=h_B(v). A path using the new edge reaches an old
descendant of v. An old predecessor y of u already has
h_B(y)>=h_B(u)>=h_B(v), so this path cannot increase its maximum. These
are all possible newly extended paths, since the relation is forward.

Put b=h_B(j), d=h_B(k). If b>=d, adding jk changes no HRV value in B.
It also changes none in B+ij: the outgoing reachability of j and k is
unaffected by adding the earlier edge ij. Hence h_B01=h_B00 and
h_B11=h_B10. If b<d, the selected ik gives h_B(i)>=d>b, so adding ij
is inert in B. After adding jk, the maximum reachable from j is d and
the maximum from i is still at least d. Thus ij is also inert in B+jk,
giving h_B10=h_B00 and h_B11=h_B01. This proves (EA2), including all
exterior predecessors.

The same diamond holds for K pointwise in every coloring. For a coloring
strict on B, its values satisfy f(i)<f(k), and

    [f(i)<f(j)] + [f(j)<f(k)]
      = 1 + [f(i)<f(j)<f(k)].                              (EA3)

Multiplying by its monomial and summing proves the identity with any
fixed endpoint colors. Equation (EA2) proves the corresponding identity
for E with the same marks, since equality of HRV maps gives equality of
their canonical chain forests. Thus both marked quantities satisfy

    X_B10[alpha,beta] + X_B01[alpha,beta]
      = X_B00[alpha,beta] + X_B11[alpha,beta],   X=K,E.      (EA4)

### Internal adjacent swaps and the DN identifications

Suppose sigma exchanges adjacent internal vertices w,x=w+1, fixes a,c,
and carries a forward relation A to a forward relation sigma A. Suppose
also that w,x are not both sinks of A. Then sigma preserves the relative
order of the sinks. Every highest reachable vertex is a sink: otherwise
an outgoing edge reaches a larger vertex. Relabeling reachability therefore
gives the exact identity

    h_(sigma A)(sigma v) = sigma(h_A(v)).                   (EA5)

It follows that sigma bijects HRV fibres and preserves their sizes,
membership of a,c and coincidence of their two fibres. Thus the endpoint
fibre data, and hence E_A[alpha,beta], are preserved. Relabeling colors
by sigma proves the marked K identity as well. This argument does not
require sigma to preserve the order of the vertices inside each fibre;
the endpoint positions and fibre sizes already determine (EA1).

For DN we have a<=u<w<x<z<=c and

    e=uw, f=wz, q=wx, r=xz, e'=ux,
    L_ij(Q)=Q+e+f+i q+j r,
    R_ij(Q)=Q+e'+r+i e+j q.

The bottom map is precisely sigma L_00(Q)=R_00(sigma Q).
There is no selected wx edge to reverse, and w is a nonsink because f
is selected. It satisfies every hypothesis of (EA5) and fixes both
endpoint marks. The top states L_11(Q),R_11(Q) have the same transitive
closure: both contain e,q,r; their additional edges f and e' are
redundant through q,r and e,q, respectively. Closure equality preserves
both quantities in (EA1). Deletion or insertion of any redundant selected
edge likewise preserves them. Identity maps, including absent-corner
deletion and changes of strict markings with the selected relation fixed,
preserve them directly.

Consequently the entire direct DN formula, including the deletion term
with coefficient delta=h10-h01, holds with both endpoint marks. The
reason for deleting f when delta is nonzero is exactly the original
cover argument; when f is redundant, its deletion preserves closure
and thus the marked quantities too. Coefficient reassembly into whole
components does not involve colors or HRV values. Hence any completed
reassembly using these identities retains both marked identities.

### Gluing whole components and their recurrences

**Theorem.** Suppose a signed recurrence for complete components on [a,c]
has been proved by diamonds, closure-preserving edge changes, identity
maps and adjacent relabelings satisfying (EA5) and fixing a,c. Suppose
all diagrams in that recurrence have the same vertex interval. Attach
ordinary diagrams on [b,a] and [c,d], with no natural edge crossing
between block interiors, and fix any complete components P,T in them.
Then the same signed recurrence holds after gluing P and T to every
component in every term. Every resulting term is a complete component.
The identities hold for K and E with the same coefficients, and may
also retain the two outer endpoint colors.

**Proof.** Every natural triangle lies in one of the three blocks. A
forward path between two vertices of that block cannot leave the block
and return, so every cover test is internal. Thus an actual flip changes
exactly one block state, with exactly the same admissibility as in that
block. The complete flip graph is the Cartesian product of the three
block flip graphs. Its components are exactly the products P*C*T.
This includes every output component and every source addition which is
subtracted in a smaller diagram.

For fixed colors alpha,beta at a,c, strict colorings glue independently.
Use K_P with the weight of a omitted, K_C[alpha,beta] with both endpoint
weights present, and K_T with the weight of c omitted. Their product
counts each vertex once. Summing alpha,beta gives K_(P*C*T). Keeping the
colors at b,d throughout gives its outer-marked version.

For E we use the identical construction on the canonical chain forests,
with the attachment factors E_P,E_T rather than K_P,K_T. We check this
from the actual HRV maps. For two blocks meeting at v, the vertices of
the left block whose HRV is v acquire the right HRV of v. Every other
left fibre is unchanged; every right HRV is unchanged. Thus precisely
the two fibres containing v merge. The left chain ends at v and the
right chain starts at v, so their union is the increasing chain of the
merged fibre. Applying this argument twice handles three blocks, even
when the two middle endpoint fibres coincide.

Every generator of the stated middle recurrence preserves the marked
identities (EA1), by (EA2)--(EA5) and closure invariance. Multiplying the
marked K identity by the two K attachment factors and summing its marks
gives the glued K recurrence. Multiplying the marked E identity by the
two E attachment factors gives the glued E recurrence. The integer
coefficients are the same in both. We do not assume K_P=E_P or K_T=E_T,
nor any marked or unmarked component expansion for an attachment. This
proves the theorem.

For the established DN steps, the induction order is also preserved.
Attaching fixed blocks adds the same vertices and area to every term.
If s vertices are inserted before the middle, the middle moment changes
from M to M+sA, up to a fixed contribution from the attachments. A
strict decrease in A remains strict; when A is unchanged, a strict
decrease in M remains strict. Thus these are still recurrences into
strictly smaller diagrams under (n,A,M).

### The attached five-vertex table

Every identity in the complete left table uses the DN bottom map
exchanging 2,3, diamonds, and deletion of the absent corner 13 in the
added I-components. These operations fix 0,4 and satisfy the theorem.
Consequently all fourteen source-component recurrences in that table
extend to arbitrary endpoint attachments, without restrictions on the
sizes, cycle ranks or components of those attachments.

For the fixed check, attach the triangle component

    P={02+01,02+12}

on the left, shift the middle vertices by 2, and attach its translate
T={68+67,68+78} on the right. The three global areas are

    L: 012122212,       R: 012123112,       J: 012121212.

Their strict edges are respectively {02,24,46,68}, {02,25,56,68}, and
{02,24,46,68}. The five rows with the shifted corner 35 selected have
the following component sizes. Commas separate distinct components.

| Middle source | Glued source | Glued targets in R | Subtract in J |
| --- | --- | --- | --- |
| C_0 | 4 | 4 | 0 |
| C_1 | 16 | 32 | 16 |
| C_2 | 24 | 20, 8, 4 | 8 |
| C_3 | 16 | 12, 4 | 0 |
| C_4 | 4 | 4 | 0 |

All nine corner-absent components delete identically to J. The exact
check starts from these products, runs the existing actual-flip BFS from
each seed, and verifies equality with each proposed whole component.
It checks every strict edge and compares signed multisets of endpoint
fibre data, both before and after attachment. This is stronger than
checking only the unmarked HRV partitions. Across the fixtures the BFS
visits 128 distinct L states, 88 R states and 64 J states. It does not
enumerate the other states of the nine-vertex diagrams. The C_1 row has
exactly the proposed 16/32/16 sizes.

Related Rust: the bounded external consumer `dn_joint_span` now has
`--endpoint-attachments`. It reuses `component_source_probe::component`
and `flip`, and the maintained `sym_poly_sym::llt::highest_reachable_vertices`
API at Rust commit `d53fb193af3c69adedbd9ec8592f87235d809ffa`.
No new polynomial sequence or maintained Rust implementation was added.
Frozen sources and the exact command/output are recorded under
`/lake-cache/ai-projects/requests/VerticalStripLLT/endpoint-attachments-20260929/`.

### Remaining boundary

The theorem requires complete middle components and a proved middle
recurrence. It does not collect pieces left by a DN move with crossing
exterior edges, and it does not independently reduce extra source
components in a general homogeneous completion class. Those are still
the missing parts of the general diagram-recursion proof. The NN bottom
swap can move a marked endpoint, so it does not automatically satisfy
this theorem's hypothesis. No NN endpoint extension is asserted here.

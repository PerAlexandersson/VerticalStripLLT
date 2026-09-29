# Redistributing one component through an NN move

2026-09-28. We follow the author's proposed argument: split one component
using the diagram recurrence, apply further diamonds, and collect complete
components in smaller diagrams. We do not require it to be isolated inside
an auxiliary union of source components. The example and local transport
below are proved; the uniform reconstruction for arbitrary components
remains to be found.

The [unicyclic NN theorem](COMPONENT_NN_LEFT_REASSEMBLY.md) now completes
this construction for connected components of cycle rank one. It combines
the split below with whole-tree corrections and both overlap repairs.

The [overlap analysis](COMPONENT_NN_OVERLAPS.md) proves that this initial
image already has constant coefficients across every flip preserving ab.
Only two overlapping-triangle geometries need further redistribution.

The [four-edge case table](COMPONENT_FOUR_EDGE_CASES.md) gives a shorter
repair of the canonical image for the five-state example below: one
redundant-edge equality completes two target components simultaneously.

Write [T] for either the strict-coloring enumerator K(T) or the HRV elementary
expression E(T). All sums are unweighted. These state valuations depend on
the full selected relation, not on which selected edges are marked strict.
Every equality below uses the same coefficients for the two valuations.

## A complete example using three diamonds

Take area (0,1,2,3), with strict corner 03. For readability put

    a=01, b=02, c=12, d=13, e=23, f=03.

Here the letters denote edges, and juxtaposition denotes a selected set.
The five orientations

    C = {fabc, fabd, fbcd, fbde, fcde}

form a complete component. Delete corner f. The smaller diagram has area
(0,1,2,2), with all its edges normal. Its following four sets are complete
components:

    D1 = {abd, bcd, bde},       D2 = {abcd, abde, bcde},
    D3 = {be},                 D4 = {abe, bce}.

We prove

    X(C) = X(D1) + X(D2) + X(D3) − X(D4),    X=K,E.       (1)

First apply the source diamond with retained edge f and exchanged shorts
a,d:

    [fabc]+[fbcd] = [fbc]+[fabcd] = [bcd]+[abcd].

The last equality swaps vertices 0,1 in the first term and removes redundant
f in the second. The other three orientations give

    [fabd]=[abd],       [fbde]=[bde],
    [fcde]=[fce]=[bde].

For the last equality we first remove d, which is redundant through c,e,
and then swap vertices 0,1. These swaps preserve both valuations: they
relabel the entire selected relation, and both swapped vertices are
nonsinks, so the labeled reachable sinks and HRV fiber sizes are preserved.
We have now obtained

    X(C) = X(D1) + [abcd] + [bde].

The last two terms are incomplete pieces. We redistribute them using two
diamonds in the smaller diagram, both retaining b and exchanging a,c:

    [abde]+[bcde] = [bde]+[abcde],
    [abe]+[bce]   = [be]+[abce].

Since d is redundant through c,e, we have [abcde]=[abce]. Subtracting the
second diamond from the first gives

    [bde] = [abde]+[bcde]+[be]−[abe]−[bce].

Substitution proves (1), with all resulting terms grouped into the displayed
complete components. Thus the extra diamond moves do exactly the required
reassembly. This example uses no component-expansion theorem as an input.

## The initial NN split for any one component

Return to vertex labels a<b=a+1<c, with strict corner ac, and retain all
eligible ordinary NN hypotheses. Put q=ab and r=bc. Let Q be the common
exterior selection and let σ interchange a,b. Use L_ij(Q) for the four
source states with bits q,r, and let h_ij(Q) indicate membership in the
single component C under consideration.

Let D0=L-ac be the corner-deletion diagram. Its natural graph is that of
the shortened NN target R, but r remains normal in D0 and is strict in R.
Write D0_ij(Q) for its states. The selected-r sector is exactly the union
of complete components identified with R. This permits us to do the entire
redistribution in D0 and split off the R components afterwards if desired.

Put δ=h_10−h_01. If ac covers in L_10, then L_10↔L_01 is an actual flip.
Indeed, ab is adjacent; an alternate b-to-c path would contradict the
coverhood of ac after ab is included; and adding bc after removing ab
cannot make ac redundant, since no a-to-b path remains. Component membership
therefore gives δ=0. Consequently, whenever δ is nonzero, ac is redundant
in L_10 and can be deleted from that state without changing either valuation.

The source diamond and the ordinary NN endpoint identifications now give

    X_L(C) = Σ_Q (h_00(Q)+h_01(Q)) [D0_01(σQ)]
             + Σ_Q (h_11(Q)+h_01(Q)) [D0_11(Q)]
             + Σ_Q (h_10(Q)−h_01(Q)) [D0_10(Q)].        (2)

This is an exact split of the original component into smaller-diagram
orientations, for both K and E. In particular, it retains the unmatched
middle orientations instead of enlarging C to force a pairing. What remains
is to redistribute the right side into whole components, as in the example.

The further source identity [L_01(Q)]=[L_01(σQ)] can also be used in that
redistribution. Both ac and bc are selected, so σ conjugates the entire
selected relation and fixes every sink label. Marking ac rather than bc
strict is irrelevant to this unweighted equality. We do not assert equality
of decorated diagrams or preservation of source component membership.

## The two remaining coefficient comparisons

We keep the indicator h of the single component C throughout. The initial
image (2) has coefficients

    w₀₀=0,                    w₁₀=h₁₀−h₀₁,
    w₀₁=(h₀₀+h₀₁)∘σ,         w₁₁=h₁₁+h₀₁.

These are already constant across every target flip preserving q, by
[the overlap lemma](COMPONENT_NN_OVERLAPS.md). Since r is maximal in D0,
no target flip exchanges r. Thus only the following two geometries remain:

| Target overlap | P | Q | Retained edge | Exchanged edges |
| --- | --- | --- | --- | --- |
| Left, t<a<b<c | T+tb | T+ta+tb | tb | ta, q |
| Right, a<b<d<c | T+ad | T+ad+bd | ad | bd, q |

Here T includes the other strict edges, and the displayed target flip is
assumed actual. For either row and j=0,1, put

    Uⱼ=D0_0j(Q),       Vⱼ=D0_1j(P),
    Δⱼ=w(Vⱼ)−w(Uⱼ),   H=h₀₀+h₀₁.

Adding the maximal source corner lifts the target flip, giving
h₁₀(P)=h₀₀(Q) and h₁₁(P)=h₀₁(Q). Substitution gives the SAME bookkeeping
for both overlap types:

    Δ₀=h₁₀(P)−h₀₁(P),
    Δ₁=h₀₁(Q)+h₀₁(P)−H(σQ),
    Δ₀+Δ₁=H(Q)−H(σQ).                              (3)

Thus the remaining work is to repair these coefficients and collect whole
target components. A repair must have zero valuation for both K and E;
diamonds, redundant-edge equalities and the allowed adjacent relabelings
supply such identities. Once the repaired coefficients agree across every
target flip, choose one representative of each complete target component
D. Its common coefficient m_D gives

    X(C)=Σ_D m_D X(D),       X=K,E.

This is the desired component recurrence, in the smaller diagram D0.
It does not require proving that C is isolated in a larger source packet.
After a local repair, agreement across other incident flips must still
be checked; the initial q-preserving constancy cannot simply be assumed
to survive arbitrary changes of coefficients.

The recent unicyclic arguments are available precisely where (3) compares
source memberships. The [middle-join theorem](COMPONENT_NN_MIDDLE_JOINS.md)
and [inactive corrections](COMPONENT_NN_INACTIVE_CORRECTIONS.md) control
the middle term. The [incoming-bridge repair](COMPONENT_NN_FIRST_JOINS.md)
and new [sink swap](COMPONENT_NN_SINK_REPAIR.md) identify further first-join
pieces. These are supporting repairs, with their stated hypotheses; a
uniform repair of (3) for every component is still missing. The five-state
calculation above and its [sixteen-case table](COMPONENT_FOUR_EDGE_CASES.md)
show the complete push, repair and collection in a proved example.

The [tree-sector calculation](COMPONENT_NN_TREE_SECTORS.md) now proves a
uniform recurrence for the connected source tree component: its image is
exactly a union of complete smaller forest components, each with coefficient
one. For an arbitrary source component, every connected target tree component
selecting r already has a constant coefficient in this initial split.

For a connected unicyclic source component, the
[simultaneous inactive-corner repair](COMPONENT_NN_UNICYCLIC_REASSEMBLY.md)
completes every r-absent piece and preserves all q-preserving equalities.
The selected-r tree and disconnected sectors are already whole; target
components inactive at r are now proved whole too. Only connected target
unicyclic components active at r can still require repair. This does not
settle the remaining first mixed comparisons or higher cycle ranks.
The [active-component swap](COMPONENT_NN_ACTIVE_SWAP.md) subsequently settles
the right first comparison in cycle rank one, leaving its left counterpart.

## What Rust has checked

We reused the existing Rust cover-flip model, the maintained exact sparse
linear algebra in `sym-poly-core`, strict P-partition enumerators in
`sym-poly-qsym`, and HRV maps in `sym-poly-sym`. No new polynomial generator
or replacement graph enumerator was introduced.

The first calculation allowed the distinguished NN diamond, the preceding
source swap, and deletion of redundant ac. It found integral expressions in
complete D0 components for all 3 components of area (0,1,2), all 15 components
of area (0,1,2,3), all 18 components of area (0,1,2,3,2) at corner 03,
and three selected components of the six-vertex diagram below. The example
(1) is a short hand proof extracted from one of these exact certificates.

In area (0,1,2,3,4,3), with strict corners 04,25 and NN corner 25, four
further tested components required additional redistribution. Starting with
(2), we allowed actual diamonds in D0, equality of transitive closures, and
adjacent relabelings that remain in D0 and preserve the order of sinks.
All four then admitted expressions in complete D0 components. Ordering the
component columns differently in the exact linear solve gives the following
shorter, positive integer expressions, improving the first rational answers.
Here C_m and D_m denote the complete components containing full-edge mask m
in the source and deletion diagrams, respectively:

| Source component | Expression in smaller components, for both K and E |
| --- | --- |
| C_767 | D_1151 + D_1279 + D_1499 + 2D_2303 + 5D_2751 + 4D_3709 |
| C_1979 | D_1471 |
| C_1023 | D_1279 + D_1535 + 2D_3711 |
| C_2043 | D_1535 |

The deletion diagram has area (0,1,2,3,4,2) and strict corner 04. Masks
use the sorted full natural-edge list of the respective diagram, including
strict edges; they are not normal-edge masks. These are exact finite
certificates from the permitted relations. We have not yet extracted short
hand proofs of the table or a uniform redistribution rule.

For every successful expression we independently evaluated the same
coefficients on both sides: strict P-partition generating functions agreed
exactly in the fundamental basis, and HRV expressions agreed exactly in the
elementary basis. Thus these checks cover every alphabet, not just a small
numerical specialization. The relation calculations also independently
certify the expressions from the permitted local identities.

There are 177 source components and 362 deletion-diagram components in that
six-vertex example. The initial calculation tested seven source components;
the complete `--six-all` run now tests all 177. Exactly 173 admit the first
local construction; the other four are precisely those in the displayed
table (indices 31,47,38,50). The expanded relations suffice for all four.
All 177 resulting expressions have integer coefficients, with independent
exact K and E checks. This is exhaustive for this diagram, not for arbitrary
diagrams or degrees. The new receipt is `nn-all-components/six-all.jsonl`
under the external request cache. The earlier restriction to target
diamonds alone was insufficient for the chosen initial split; this is not
an obstruction to the author's proposed argument.

External source:

    diamond-exploration/hrv-bridge/src/bin/nn_component_transport.rs

under `/lake-cache/ai-projects/requests/VerticalStripLLT/`. The receipt
`recurrence-continuation/nn_rust_transport_certificates.jsonl` retains the
first coefficients; its `.log` records the five-state example and the
allowed relation counts. The improved table is in
`nn-overlap/nn_rust_small_certificates.jsonl`. Each receipt directory has
source and receipt hashes. The earlier source is preserved as
`recurrence-continuation/nn_component_transport-at-c83dffb.rs`; the source
used for the improved table is copied into `nn-overlap/`. Each Rust run
used a 600-second cap and reduced priority.
No shared Rust source, Lean source, or manuscript file was changed.

Astra derived and audited the direct split, the local redistribution
equations, and the three-diamond example. Luna independently checked (2),
with the unweighted marking convention made explicit. Primary checked the
proofs, reused the Rust APIs, and verified the exact expressions.

## Exact completion within one selected-edge layer

2026-09-29 continuation. The initial split admits the same kind of exact
homogeneous completion as the
[direct DN split](COMPONENT_DN_SOURCE_ADDITIONS.md#completing-one-selected-edge-layer-of-the-direct-dn-image).
We prove the smallest required source union, without claiming that all
of its extra components are independently reducible in general.
No new independent review is asserted for this continuation.

Fix a total selected-edge count k. Let m be an integer function on complete
k-edge source components, extended by zero to other layers. Apply the
initial split linearly to m. Since the source selects f=ac and D0 omits
it, the coefficients separate as follows:

| D0 state and selected-edge count | Coefficient |
| --- | --- |
| D0_01(Q), size k | m_00(sigma Q) |
| D0_11(Q), size k | m_01(Q) |
| D0_01(Q), size k-1 | m_01(sigma Q) |
| D0_11(Q), size k-1 | m_11(Q) |
| D0_10(Q), size k-1 | m_10(Q)-m_01(Q) |
| Every other state | 0 |

For example |D0_01(Q)|=|Q|+1, while |L01(Q)|=|Q|+2.
These offsets explain why the two summands of w_01 or w_11 never
contribute simultaneously for a fixed source layer. We are grading states
by selected edges, not separating polynomial degrees in K or E.

On the r-selected sector define two source lifts:

    psi_0(D0_01(Q))=L00(sigma Q),
    psi_0(D0_11(Q))=L01(Q),
    psi_1(D0_01(Q))=L01(sigma Q),
    psi_1(D0_11(Q))=L11(Q).

The first preserves the selected-edge count; the second raises it by one.
Impose the following equalities on actual k-edge source components:

1. For every actual r-selected D0 flip T<->T' at size k, equate the
   components of psi_0(T),psi_0(T').
2. For every actual r-selected D0 flip T<->T' at size k-1, equate the
   components of psi_1(T),psi_1(T').
3. If an r-absent D0_10(Q) of size k-1 has an actual flip removing q,
   equate the components of L10(Q),L01(Q).

Let V_k(C) be the equivalence class of C generated by these pairs.

**Theorem.** The unmodified direct NN image of m is constant on every
complete D0 component if and only if m is constant on every class V_k(C).

**Proof.** The edge r is a natural corner of D0, so its selected status
cannot change along a flip. In its selected sector the first four rows
of the table identify all comparisons exactly with items 1 and 2.
In its absent sector, only the q-selected states of size k-1 can have a
nonzero coefficient. Every q-preserving comparison keeps
m_10(Q)-m_01(Q) constant by the proved full-exterior
[overlap lifts](COMPONENT_NN_OVERLAPS.md#which-flips-remain).
An exit removing q has coefficient zero at its other endpoint and is
therefore equivalent to item 3. All other states have zero coefficients.
This proves both necessity and sufficiency, including exterior flips.

Taking the indicator of V_k(C) gives, for both X=K,E,

    sum_(I in V_k(C)) X_L(I)
      = sum_(B a whole D0-component) c_B X_D0(B),
      c_B in {-1,0,1}.                              (4)

The r-selected output coefficients are nonnegative; a negative coefficient
can occur only in the r-absent sector. The source union V_k(C) is minimal
among unions at selected-edge count k which contain C and whose unmodified
direct images have whole components. More generally, any such integer
completion with m(C)=1 has m(I)=1 for every I in V_k(C), by the generating
equalities. These are the same elementary closure and minimality arguments
as for DN.

If each extra I has an independently proved recurrence in whole smaller
components, subtract those recurrences from (4). This isolates C, with
the same coefficients for K and E. D0 has one fewer natural edge, so
all of its components are smaller for the ordinary induction. For a
specified collection A of independently reduced source components, this
homogeneous source-addition construction succeeds exactly when
V_k(C) minus {C} is contained in A. No general assertion of that
containment is proved here. In particular, this result does not replace
the remaining individual-component theorem by a theorem about unions.
Mixed-layer additions or further output diamonds remain allowed if this
particular construction does not suffice.

### The five-state example revisited

For C={fabc,fabd,fbcd,fbde,fcde} above, its minimal class adds exactly

    I={fabe,fbce}.

The only flip in I exchanges a,c while retaining b. The corner f is
redundant throughout via b,e, and the other possible flips either lack a
retained long or attempt to retain redundant f. Thus I is a whole source
component. Deleting f identifies it with the whole two-state D4 from (1).

The direct image of C+I is already complete. Written using the D1,D2
above and three singleton components, it is

    X(C)+X(I)=X(D1)+X(D2)-[ace]+[cde]+[acde].        (5)

The three singletons are complete because every selected nonadjacent edge
in each is redundant. Their equalities [acde]=[ace] and [cde]=[be]
follow respectively by deleting redundant d, and by deleting d followed
by the adjacent interchange 0,1. Subtract X(I)=X(D4). This recovers (1)
from the homogeneous source-addition construction. No individual source
path is asserted between C and I; adding the whole deletable component
is the mechanism that repairs the output boundary.

### Verification

Related Rust: the existing external `first_join_tree_lifts.rs`, option
`--nn-homogeneous-closure`, reuses `nn_component_transport::{components,
valuations}` and the established cover/flip oracle. In the fixed complete
four-vertex source it checks all 32 states in 15 source components. The
eight actual target comparisons give one homogeneous pair edge and 14
classes. For every class, all output coefficients are constant on whole
components and belong to {-1,0,1}; both K and E identities are checked
exactly. It recovers the five-/two-state class and all terms of (5), and
checks that the added component is inactive at f. No diagram-family scan,
new polynomial generator, maintained Rust change or Lean/Lake build is used.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/homogeneous-dn-closure-20260929/`.

## A shorter repair entirely in the NN right-hand diagram

2026-09-29. The user reiterated the direct task: start with one complete
component on the left, follow its image through a recurrence, and use
diamonds and relabeling until the result is a linear combination of whole
components on the right. Source additions and uniqueness assumptions are
optional methods for obtaining that identity. They are not hypotheses of
the desired general statement.

The four-vertex example at the start of this note has a shorter repair
which stays in the actual shortened NN target throughout. Retain

    a=01, b=02, c=12, d=13, e=23, f=03,
    C={fabc,fabd,fbcd,fbde,fcde}.

The source is the complete natural diagram with strict corner f. Its
shortened NN target R has natural edges a,b,c,d,e and strict corner d.
The initial source diamond and endpoint maps already give

    X(C)=X(D1)+[abcd]+[bde],
    D1={abd,bcd,bde},                         X=K,E.       (R1)

For completeness, pair fabc and fbcd by the diamond retaining f. Its
empty and full terms map to bcd and abcd, respectively, by swapping
0,1 and deleting redundant f. Of the other source terms, fabd deletes
f to abd, and fbde deletes f to bde. In fcde, first delete d, redundant
through c,e, and then swap 0,1; this also gives bde. Thus (R1) keeps
the multiplicity of each output term, including the second copy of bde.

Now use just ONE additional diamond in R, retaining b and exchanging
a,c, with d,e fixed:

    [abde]+[bcde]=[bde]+[abcde].                         (R2)

In its full term b is redundant through a,c, so [abcde]=[acde]. Hence

    [bde]=[abde]+[bcde]-[acde].                         (R3)

Substituting into (R1), the terms collect as

    X(C)=X(D1)+X(D2)-X(T),
    D2={abcd,abde,bcde},    T={acde}.                    (R4)

These are three complete components of R, all selecting its strict edge d.
The only natural triangles of R are 012 and 123. Testing their two possible
exchanges gives exactly the paths

    abd <-> bcd <-> bde,
    abcd <-> abde <-> bcde.

There is no other neighbor of any of these six states. At acde, the only
selected possible long edge d is redundant through c,e, while b is absent,
so T is isolated. This proves both connectivity and completeness of every
right-hand component, independently of its valuation.

All source states have three selected normal edges. The corresponding
counts in D1,D2,T are two, three, three. If F denotes the component
contribution weighted by t to the number of selected normal edges, (R4)
therefore gives the polynomial identity

    F(C)=t F(D1)+F(D2)-F(T).                            (R5)

There is no division by t. The HRV sums on the right are respectively
e_(2,2)+e_(3,1)+e_4, e_(3,1)+2e_4, and e_4. They give the same
e_(2,2)+2e_(3,1)+2e_4 as the original four-component repair.

The local identity (R3) also holds with any common exterior relation
adjoined to every term: its proof uses a diamond and the selected
two-edge path a,c, with no cover assumption. What does not follow merely
from this identity is the five-vertex-or-larger analogue of the component
check after (R4). A flip involving an exterior vertex can change one of
the displayed edges and leave the proposed collection. The general task
is to choose further RHS diamonds and relabelings so that all such
boundaries close. It does not require proving that the source is unique
in an edge-count layer, or that a prescribed source-completion method works.

Related Rust: the existing external `nn_component_transport` consumer,
option `--four-vertex-rhs-only`, checks C,D1,D2,T by full actual-flip BFS,
checks their strict-edge status and ascent counts, and verifies (R3),(R4)
separately for exact K and E using the maintained APIs. It passes, including
the source HRV profile. The source has five states and the outputs have
three, three and one. No extra source component, family scan, maintained
Rust change or Lean build is used. Frozen sources and build/check output:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-rhs-only-20260929/`.

## Eliminating every unmatched term into the actual RHS

2026-09-29. The following local theorem holds with arbitrary exterior
selection. It removes the r-absent terms in (2), using at most one extra
diamond each. It does not yet collect the resulting terms into components.

Write w=a, x=b=w+1, z=c, so f=wz, q=wx and r=xz. We use

    R0(Q)=Q+r,                 R1(Q)=Q+q+r.

Here Q excludes f,q,r and contains the common strict edges. Assume f is
redundant in Q+f+q, as it must be whenever delta(Q) is nonzero. Then:

* If x reaches z in Q, we have

      [Q+q]=[R1(Q)].                                      (E1)

* Otherwise, choose the first edge alpha=wt of any selected w-to-z
  bypass in Q+q. Put beta=xt. Then

      [Q+q]=[R0(sigma Q)]
             +[R1(Q-alpha+beta)]-[R0(sigma Q+alpha)].       (E2)

Both statements hold for K and E. Every term on the right belongs to the
actual shortened target, including its strict r. The two natural short
edges alpha,beta are normal, so common strict edges are retained.

**Proof.** In the first case r is redundant, proving (E1). In the second,
a bypass cannot start with q: that would give x a path to z. It therefore
starts with wt for x<t<z, and its remaining t-to-z path lies in Q. The
natural interval under f contains both wt and xt. Moreover beta is absent
from Q, or x would already reach z. Since f is a natural corner, neither
alpha nor beta can be a strict corner of the source.

Apply the diamond retaining alpha and exchanging q,beta. Its full term
has redundant alpha through q,beta. Thus

    [Q+q]=[Q]+[Q-alpha+q+beta]-[Q+beta].                  (E3)

In the first term, swap w,x. The selected bypass becomes an x-to-z
path, so we may insert r. In the middle term, beta and the unchanged
suffix already give that path, and again we insert r. In the last term,
swap w,x: its selection becomes sigma Q+alpha, and sigma Q contains the
same x-to-z bypass. Insert r there as well. This proves (E2).

The swaps act on the ENTIRE exterior relation. They are forward because
q is absent in the terms being swapped. In the first term w is a nonsink;
in the last both w and x are nonsinks. Swapping adjacent vertices with at
least one nonsink preserves the relative order of all sinks, so it preserves
the HRV fibre partition. It also preserves K by the induced vertex
relabeling. The eligible NN hypotheses ensure that sigma Q is an allowed
common exterior and retains the common strict set, exactly as in the
original bottom map. No cover hypothesis is used for the diamond in (E3),
and the bypass suffix may have arbitrary length or meet arbitrary exterior
edges.

Applying (E1) or (E2) to every nonzero delta term in (2) gives an integral
state expression supported entirely in R. This proves that the auxiliary
r-absent diagram is unnecessary for state transport. Uniform collection
into whole components remains open: these changes need not preserve the
previously established coefficient equalities along q-preserving flips.

The same one-diamond proof works for DN after carrying its edge e along;
the precise formula is recorded in the
[DN continuation](COMPONENT_DN_JOINT_REPAIRS.md#eliminating-the-dn-deletion-residual).

### Finite collection checks and a relabeling distinction

We checked all components of three fixed NN diagrams and three fixed DN
diagrams, first with RHS diamonds, redundant normal-edge deletions, and
adjacent nonsink swaps. We then allowed relabelings of the reachability
poset which preserve the relative order of its sinks. These are still
valid diagram identifications: a coloring is transported by the poset
isomorphism, and the highest reachable sink is transported because sink
order is preserved. Equality of reachability relations permits redundant
edges to be inserted or deleted. The intermediate presentations need not
all lie in the fixed RHS natural graph; the resulting two states do.

| Move | Source area | Strict source edges | Source components | Locally uncollected | Uncollected with poset relabeling |
| --- | --- | --- | ---: | ---: | ---: |
| NN | 0123 | 03 | 15 | 0 | 0 |
| NN | 01233 | 03,14 | 24 | 0 | 0 |
| NN | 01234 | 04 | 116 | 7 | 0 |
| DN | 01123 | 01,14 | 15 | 0 | 0 |
| DN | 01222 | 02,24 | 14 | 0 | 0 |
| DN | 012233 | 02,14,25 | 26 | 0 | 0 |

Every one of the 210 source images has an INTEGRAL combination of whole
components in its actual RHS diagram, modulo the stated zero relations.
We also checked the final K and E identities independently and exactly.
The seven locally uncollected NN components have sizes 80,84,34,4,6,9,5.
This is an obstruction only to that restricted finite relation span;
it is not a counterexample to the recurrence. In particular, restricting
all relabeling preparations to adjacent swaps inside R is unnecessarily
strong in this example.

Related Rust: the existing external `dn_joint_span` consumer, options
`--rhs-only-audit` and `--permuted-closures`, uses the maintained sparse
rational quotient and linear-system APIs, actual-flip component enumeration,
and strict P-partition / HRV valuations. It constructs the initial images
from component indicators, checks (E1)/(E2) or their DN counterparts for
every unmatched exterior, and solves against complete RHS component
indicators. No component-expansion identity is assumed. Receipts and frozen
consumer sources are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/rhs-only-elimination-20260929/`.
These six finite checks do not prove the uniform collection theorem.

## Prepared adjacent swaps and their component boundaries

2026-09-29 continuation. The seven NN cases in the preceding finite table
do not require distant relabelings. We can use the original adjacent
contact swap after deleting the strict r when it is redundant. We now
prove how this prepared swap tracks whole components of its domain sector,
including an exact description of the possible exits. Sector components
are not asserted to be whole components of R.

Keep w<x=w+1<z, q=wx, r=xz and sigma=(w x). In the actual NN target R,
let S be the following set of states A:

    q is absent, and both w and x reach z in A-r.        (P1)

In particular, the selected strict r is redundant. Define

    Phi(A)=sigma(A-r)+r.                                (P2)

**Prepared-swap theorem.** Phi is a valuation-preserving involution of S.
It is also an isomorphism of the actual flip graph induced on S, with
arbitrary exterior selection and no cycle-rank assumption.

**Proof.** The common natural edges other than q are invariant under the
eligible NN contact swap, and all common strict edges are fixed. Removing
r avoids the one edge that would be sent to the missing f=wz. The two
paths in (P1) exchange under sigma, so inserting r in the new state is
redundant as well. Both endpoints are nonsinks. Thus redundant-edge
deletion, the adjacent relabeling, and redundant insertion preserve K
and E. The same path condition holds at the image, and applying (P2)
twice restores every selected edge.

Consider an actual flip A<->B with both endpoints in S. It cannot retain
r, since r is redundant, or exchange r, since r is a natural corner.
Deleting r changes no reachability relation or cover status of the other
selected edges. The flip also preserves the absent q. Its triangle
therefore cannot contain both w and x: for such a triangle q would be
one of the two exchanged shorts. On every other triangle sigma preserves
the order of its three vertices. Hence relabeling gives an actual flip
of the relations with r deleted. Its edges remain natural, and the
exchanged edges remain normal because common stricts are fixed.
Reinserting redundant r changes none of these covers. This gives
Phi(A)<->Phi(B). The same argument for the involution proves the converse,
including absence of any extra edges in the induced graph.

Let P be a COMPLETE connected component of this induced graph. Its image
Phi(P) is another complete induced component, and

    Z_P=sum_(A in P) [A]-sum_(A in Phi(P)) [A]=0,
                                                       X=K,E. (P3)

Adding any integer multiple of Z_P to a state expression preserves both
valuations. Its coefficients agree across every flip within S. Across a
flip with neither endpoint in S they are both zero. Consequently, a
coefficient comparison can change only at an exit from S. Such an exit
has exactly one of the following causes:

1. q becomes selected;
2. q stays absent and at least one of the two reachabilities in (P1)
   is lost.

In the second case either r becomes a cover, or the absent f would become
a cover upon insertion. This follows directly from the missing bypass,
using that q is absent and w,x are adjacent. Thus a correction on P does
not introduce uncontrolled comparisons at arbitrary exterior flips. Its
remaining boundaries are short insertion and bypass exposure. This is
more restrictive than applying unrelated state corrections, but it does
not by itself prove that these boundaries can all be closed.

### The additional relation in the complete five-vertex check

For the target with area 01233 and strict 14, the following single relation
suffices, together with the previous diamonds, normal redundant deletions
and unprepared adjacent swaps, to collect all 116 source components:

    [02+03+12+14+24]=[02+12+13+14+24].                 (P4)

Delete redundant 14 through 12,24, swap 0,1, and restore 14 through the
same two-edge path. The two states are singleton components of the induced
sector S, so (P4) is a correction of the precise form (P3). They are not
isolated in the full flip graph: each has exits of the two kinds above.
The common paths through vertex 2 make the prepared swap possible even
though directly swapping the displayed strict edge 14 would produce the
missing natural edge 04.

Modulo the 512 original zero relations, (P4) contributes one additional
independent relation. The seven previously uncollected source images now
have integral whole-RHS-component expressions. This establishes the finite
repair without general poset permutations. It does not establish that one
such relation suffices in larger diagrams.

The DN analogue includes a count-preserving channel and a second channel
which inserts a redundant strict edge; see the
[prepared DN sectors](COMPONENT_DN_JOINT_REPAIRS.md#prepared-dn-swaps-and-sector-components).
In both moves the unresolved step is now explicit for these corrections:
choose whole induced-sector corrections and RHS diamonds so that their
short-insertion and bypass-exposure boundaries cancel simultaneously.
We have not proved the existence of such choices in every diagram.

Related Rust: the existing external `dn_joint_span` option
`--prepared-sectors` verifies the state maps, both directions of every
internal actual-flip comparison, exact K/E equality, and the exit
classification in the fixed diagrams. Option `--packet-corrections`
constructs complete components of the induced sectors and uses only their
signed differences (P3), alongside the original local zero relations.
The six-diagram collection check again passes all 210 source components
with integral output coefficients. No general poset relabeling generators
are used in that check. Frozen sources, commands, logs and checksums:
`/lake-cache/ai-projects/requests/VerticalStripLLT/prepared-swaps-20260929/`.

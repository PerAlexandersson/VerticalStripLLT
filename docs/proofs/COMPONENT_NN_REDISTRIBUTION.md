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

## Descending the prepared-swap boundary identities

2026-09-29. We now give exact identities at both kinds of sector exit,
with arbitrary exterior. They track the paired actual flips and give a
strictly decreasing measure for the resulting state pairs. We have not
yet proved that these replacements collect into whole target components.

Extend the formula Phi(A)=sigma(A-r)+r to every target state with q
absent, without requiring the two bypasses. The resulting selected set
is still a valid R state. It need not have the same valuation as A.
Write Z(A)=[A]-[Phi(A)] on this larger domain. On the prepared sector
S of (P1), Z(A)=0.

### A bypass-loss exit descends by one selected edge

Suppose A in S has an actual flip to B, with q still absent. Let s be
the removed short, t the inserted short, and ell the retained long. Put

    E=A-s,          F=A+t.

Thus the actual middle states are A=E+s and B=E+t; F contains both
shorts. The following are actual flips and a valuation identity:

    Phi(A) <-> Phi(B),
    Z(B)=Z(E).                                        (B1)

In particular, both states in the pair on the right have one fewer
selected edge than their corresponding states on the left.

**Proof.** The original flip cannot retain redundant r or exchange the
strict corner r. Its triangle cannot contain both w,x, since q stays
absent. Delete r and swap its triangle, preserving its vertex order.
The swapped flip is still actual. Reinserting r, even when it is no
longer redundant at the new endpoint, does not affect the cover tests:
a path using a maximal natural corner cannot bypass a different natural
edge. Thus Phi(A)<->Phi(B), with the same full exterior transformed.

The two diamonds, with the respective retained longs, give

    [A]+[B]=[E]+[F],
    [Phi(A)]+[Phi(B)]=[Phi(E)]+[Phi(F)].

Adding the other short cannot destroy either bypass, so F belongs to S.
We have Z(A)=Z(F)=0. Subtraction proves (B1). This uses actual paired
boundary flips; it does not assume equality of source component membership
at the exposed endpoints.

### A short-insertion exit descends or increases reachability

Suppose instead that A in S has an actual flip to B which inserts q.
Its triangle is one of the two types

    h<w<x: ell=hx, s=hw;
    w<x<h: ell=wh, s=xh.

Here s is removed. In A both ell,s cover and sigma interchanges them.
Both edges are present and cover in A'=Phi(A) as well. Hence the SAME
exchange s->q, retaining ell, gives an actual flip A'->B'. For the
reverse endpoint cover, a new bypass of ell would require a path replacing
s before the exchange, contrary to its cover. The inserted q is adjacent.

Put

    E=A-s,       E'=A'-s,
    C=A+q-ell,   C'=A'+q-ell.

Two RHS diamonds, followed by deleting the redundant ell in each full
term, give

    [B]-[B'] = [E]-[E'] + [C]-[C'].                    (B2)

The long ell is normal in the eligible NN target: on the right it lies
properly inside the old f; on the left the contact row x has no strict
incoming corner. Thus all four terms on the right remain valid R states,
with every strict edge selected.

The E pair has one fewer selected edge at each endpoint. The C pair has
the same edge counts as B,B', but each has STRICTLY MORE reachability
relations. Indeed, the deleted ell is recovered through the newly selected
q,s. Every old comparison in B survives, and s adds a new one. A path
replacing s could not be created by q: in the left case q ends above
s's head; in the right case q starts below s's tail. The cover of s in
A therefore excludes that path in B. The same argument applies to B'.

For a pair (U,V), let N=binomial(n,2) and set

    mu(U,V)=(|U|+|V|, 2N-|reach(U)|-|reach(V)|),       (B3)

ordered lexicographically, with strict reachability counted off the
diagonal. Every pair on the right of (B1) or (B2) has smaller mu than
the left pair. These are finite, nonnegative measures.

This proves descent for every permitted prepared-sector boundary step.
It does NOT yet give an algorithm for all component coefficients: an E
or C pair need not itself be another prepared-sector boundary pair, and
we have not shown that every terminal remainder is a combination of whole
components. Establishing that closure, or absorbing the remainders in
other component corrections, is the remaining assembly obligation.

### An exposed endpoint need not stay in the same source component

The first-drop source 012333 has strict 03,14,25. Its ND contact at
w=2,x=3,z=5 unmarks g=03 before NN. The actual NN target has area 012332,
with strict 14,35. Consider its prepared state and its image

    A ={03,14,24,34,35,45},
    A'={02,14,24,34,35,45}.

Both roots reach 5 through vertex 4 after 35 is deleted. The paired
actual exits are

    A  --34->13 [14]--> B ={03,13,14,24,35,45},
    A' --24->12 [14]--> B'={02,12,14,34,35,45}.

The needed shorts and 14 cover at both endpoints. In B the edge 35 is
now a cover; in B' the virtual 25 would be a cover. Restoring 25 gives
two source states interchanged by sigma. They lie in DIFFERENT whole
source components: one selects the maximal natural corner 03 and the
other omits it, and no actual flip can exchange a maximal natural corner.
Thus exposure alone cannot justify setting their source indicators equal.
This example occurs in the required first-drop induction, not only in an
arbitrary unsaturated diagram.

Identity (B1) gives the valid replacement

    [B]-[B']=[03+14+24+35+45]-[02+14+34+35+45].        (B4)

The two HRV values on either side are e_6 and e_(4,2), respectively;
the difference is not zero. The proof retains it in the lower edge layer.
A source component omitting 03 is independently corner-deletable, but
turning that observation into a simultaneous whole-component repair is
an additional step, not an indicator equality.

Related Rust: the existing consumer option `--boundary-identities` checks
every paired actual exit, both diamonds, the pruned terms, exact K/E and
the strict reachability increase in (B2). The six earlier fixtures and
the first-drop six-vertex fixture pass. The latter has sixteen bypass-loss
and forty-five q-insertion exits. A separate exact source check confirms
eight failures of the exposed-swap membership assertion among its sixteen
bypass-loss endpoints. The broader source-swap probe passes 2087 exposed
states in the complete six-vertex graph; that finite success does not
remove the first-drop counterexample.

Using the existing local relations and whole prepared-sector corrections,
all 110 source components in 012333 have integral expressions in the 83
whole target components. This is one further fixed collection check, not
a proof that (B1)--(B3) form a closed general reduction. Frozen sources and
receipts are in `prepared-boundaries-20260929/` under the external request
folder. The DN continuation below treats the possible strict retained long.


## Following the swap through a further flip

2026-09-29 continuation, following the notebook's component brackets.
We keep every exterior edge and use only selected diagrams, diamonds
and vertex relabeling. The user explicitly asks us to keep this proof
in that language; basis calculations are not part of the argument.

The adjacent-swap formula

    A' = sigma(A-r)+r

defines a valid target state whenever q is absent, even after a required
bypass disappears. It need not preserve the value of that individual
state. Nevertheless it still transports every q-preserving actual flip
whose retained long is not r. The converse holds too.

Indeed r is a maximal natural corner. Removing or inserting r cannot
change a cover test for any other natural edge: a replacement path using
r would put that other edge strictly around r. The triangle of a
q-preserving flip cannot contain both w,x. Thus sigma preserves its
vertex order, transports its shorts and retained long, and preserves
both cover tests. The common strict corners remain selected. Applying
the same swap again proves the converse.

Suppose A<->B is such a flip and A'<->B' its transported flip. Write
E,E' for the two diagrams with neither short selected. Write F,F' for
the diagrams with both shorts selected and the redundant long deleted.
The two diamonds say simply

    [A]+[B]=[E]+[F],
    [A']+[B']=[E']+[F'].

Consequently, if we have already matched A with A', the next missing
pair can be dealt with by

    [B]-[B'] = -([A]-[A']) + ([E]-[E']) + ([F]-[F']). (C1)

This is valid whether or not A still satisfies the bypass conditions.
The empty diagrams have one fewer edge each. The pruned full diagrams
have the same number of edges as A,B, but strictly more reachability:
the new short was not implied before the flip, and the removed long
is recovered through the two shorts. A deleted strict long is a natural
corner; its pruned diagram is the smaller diagram with that corner
removed. We keep all other strict edges.

We may apply (C1) successively along a spanning tree of a complete piece
of the target flip graph with q-insertion and r-retaining flips removed.
If the piece contains a prepared state, its initial matched difference
is zero. Repeated substitution expresses the difference of the two
complete pieces as an integer sum of the empty and pruned-full pairs.
This includes the bypass-loss flips inside that piece. No division is
used: starting with coefficient 1 at each vertex, eliminate a leaf by
(C1), subtract its coefficient from its parent, and continue.

The remaining comparisons are precisely the omitted q-insertion and
r-retaining flips. Pieces without a prepared starting state are not
settled by this argument. Nor have we shown that the new signed terms
assemble into whole target components. We must keep the terms from the
original source component together and finish those comparisons.

Related Rust: the existing consumer's `--extended-packets` option checks
the paired flips in both directions and the complete-piece identities
in the six earlier diagrams, the first-drop six-vertex example and the
attached eight-vertex DN example. It also checks the edge and reachability
changes. These are checks of the stated diagram lemma, not evidence that
the missing whole-component assembly has been proved. Frozen receipts:
`coupled-coefficients-20260929/` under the external request folder.

## The NN statement also suffices for DN

2026-09-29 continuation. The new
[empty-corner DN reduction](COMPONENT_DN_JOINT_REPAIRS.md#dn-through-an-empty-corner-nn-diagram)
shows why a uniform NN collection theorem would settle both remaining
cases. Add the missing DN corner empty and unmark the neighboring
selected corner. This preserves the SAME whole source component and
makes the contact NN. Once its image has been collected into whole NN
target components, marking selected exposed corners and deleting absent
ones sends each whole component to the DN target or a smaller deletion
diagram. These are the notebook's identity maps.

The qualification is that NN must allow this empty unmarked corner and
need not be applied at the first area drop of the enlarged diagram.
The existing saturated unicyclic theorem is insufficient for that
hypothesis. We have proved the reduction, not the uniform NN collection
it assumes. No polynomial basis enters the argument.

## A complete component certificate beyond cycle rank one

2026-09-29 continuation. We keep the proof in terms of the notebook's
component brackets. The former finite checks already included this
five-vertex example; here we give a certificate using only whole
components, the NN diamonds and redundant-corner deletion. No polynomial
or basis calculation is used in this certificate.

Take the complete natural graph on 0,...,4 with strict f=04, and let C
be the whole component containing

    A={01,02,03,04,12,24}.

It has 84 states, all connected with six selected edges, hence cycle
rank two. Put q=01, r=14. Let R have area 01233 and strict 14; let D
have the same natural graph and no strict edges.

For each row of the following table, the term means the WHOLE component
containing the displayed seed, in the specified diagram. The size helps
identify and verify it; we do not take just the displayed seed.

| Sign | Diagram | Seed | Component size |
| --- | --- | --- | ---: |
| + | R | 01,02,03,12,14 | 34 |
| + | R | 01,02,12,13,14 | 16 |
| + | R | 01,02,03,12,13,14 | 32 |
| + | R | 01,02,12,13,14,23 | 9 |
| + | R | 12,13,14,23,24 | 3 |
| + | R | 01,02,13,14,34 | 3 |
| + | R | 12,13,14,23,34 | 1 |
| + | R | 12,14,23,24,34 | 1 |
| - | D | 01,02,12,13,24 | 6 |
| - | D | 01,02,03,12,34 | 5 |
| - | D | 01,02,03,23,34 | 2 |
| - | D | 01,02,23,24,34 | 2 |

For both X=K,E, X(C) is the signed sum of these twelve whole-component
terms. In particular every term belongs to the smaller NN corner-deletion
graph; the first eight also belong to the actual strict-r target.

Here is the diagram certificate. Close C under the middle and target-flip
joins from the proved [NN component reconstruction](COMPONENT_RECURRENCE_REDUCTION.md#an-nn-recurrence-in-complete-component-sums).
In this fixed graph the resulting union consists of C and twelve other
whole components I, of sizes

    6,2,3,5,3,2,2,1,1,1,2,1.

The edge 04 is redundant at EVERY state of each I. Deleting it maps I
identically to a whole component of D. The reconstruction theorem,
which pairs middle states by diamonds and relabels the empty endpoint,
sends the 113-state union to sixteen whole R components. Subtract the
twelve deleted components. In eight of them, 14 is also redundant
throughout after deletion. Inserting 14 maps each of those eight whole
components to one of the positive R components and cancels it. This
leaves exactly the displayed table, with 99 positive and 15 negative
states. The count 99-15=84 is a consistency check, not the proof of the
valuation identity.

The complete source joins, constancy of every target coefficient, all
inactive-corner claims, exact deletion/insertion component maps and the
final table are checked by finite actual-flip enumeration. The same
coefficients work for K,E because each step of the certificate is one
of the already-proved diagram identities. This replaces an algebraic
span check for this example by an explicit component certificate. It
does not show that such inactive additions always suffice.

### Why we cannot require a path which keeps q selected

The middle mate of A is

    B={02,03,04,12,14,24}.

Both lie in C. However A has no actual flip which keeps q selected,
and its only neighbor still has f redundant. To expose f one must
first leave that stratum. For example, the first two moves below expose
04; the complete path verifies that the middle mate belongs to C.
Each row retains the indicated long edge and replaces the indicated short.

| Retain | Remove | Insert |
| --- | --- | --- |
| 03 | 01 | 13 |
| 03 | 02 | 23 |
| 04 | 24 | 02 |
| 02 | 12 | 01 |
| 04 | 01 | 14 |
| 04 | 02 | 24 |
| 03 | 13 | 01 |
| 03 | 23 | 02 |
| 02 | 01 | 12 |

This refutes the stronger proposed shortcut that every active middle
state can reach an exposure while preserving q up to the last move.
It does not refute middle membership, which this path proves in the
example, or the general exposure lemma with its stated hypotheses.
We use the whole-component certificate above for collection, rather
than imposing a q-preserving path as an extra requirement.

Related Rust: `dn_joint_span --nn-middle-slices` uses the existing actual
flip/component model only. In five fixed diagrams it checks 1698 source
components and 8616 middle states. All 6469 middle states in components
where f is exposed somewhere have their mates in the same component.
Of these, 574 cannot reach an exposure by keeping q selected until the
last move. These counts are finite evidence; the corresponding general
middle-membership assertion remains unproved. The code also verifies
every step of the complete 84-state certificate above. Frozen sources,
commands and receipts are in `nn-middle-slices-20260929/` under the
external request folder.

## NN recurrences extend at the fixed right endpoint

The endpoint-attachment argument does have a useful NN version, even
when the bottom swap moves the left endpoint. We attach only at the
RIGHT endpoint, which that swap fixes.

**One-end attachment theorem.** Suppose a signed component recurrence
on [a,c] has been proved by diamonds, redundant-edge changes, identity
maps and sink-order-preserving relabelings which fix c. Attach any
ordinary diagram on [c,d], with no natural edge crossing between the
two interiors, and choose any whole component T in the attachment.
Then the same signed recurrence holds after gluing T to every term.
Every resulting term is a whole component. No component expansion for
T is assumed.

Every natural triangle lies in a single block. A directed path between
two vertices of that block cannot leave and return, so the cover tests
are unchanged. Hence the full flip graph is the Cartesian product of
the two block graphs. Gluing takes whole components to whole components.

For K, keep the color at c fixed throughout the middle calculation.
Diamonds, redundancy and the relabelings fixing c preserve the identity
with that color fixed. Multiply by the corresponding attachment sums,
counting the weight of c once, and then sum its color.

For E, retain the size of the HRV fibre containing c as distinguished
from the other fibre sizes. Diamonds preserve the multiset of entire
HRV maps, as proved in the
[endpoint audit](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#diamonds-preserve-full-hrv-maps).
Redundancy preserves them, and each allowed relabeling fixes c and
preserves sink order, hence preserves these distinguished fibre data.
On gluing, exactly the two fibres containing c merge, counting c once;
all other fibres stay unchanged. This gives the attached E identity
with exactly the same integer coefficients. These facts prove the
claimed extension without assuming the unmarked identity implies its
marked version.

Every relabeling in the 84-state certificate swaps 0,1 and fixes 4.
It therefore extends to arbitrary chosen components attached at 4.
The added block contributes the same area and moment to each diagram,
so the decrease in the induction order is retained. In particular this
is a family with arbitrary right exterior, not just a single finite
example. It does not allow exterior edges crossing into the middle or
an attachment at a left endpoint moved by the swap.

For the fixed check, attach the two-state triangle component

    T={46+45,46+56}.

The source area is 0123412 and the target/deletion area is 0123312.
The source has strict 04,46; R has strict 14,46; D has strict 46.
Actual-flip searches verify all thirteen products (one source and twelve
signed outputs) as whole components. Their sizes are 168 on the source,
198 in the positive terms and 30 in the negative terms. The general
attachment proof above is the justification beyond this fixed check.

The general NN collection theorem, and therefore the DN consequence,
remain open. This continuation supplies a direct component certificate
and its right-end extension, not a claim of uniform reassembly.

## Using DN to separate two surviving NN components

2026-09-29 continuation. The inactive additions in the preceding example
do not suffice for the standard same-layer completion in every empty-corner
source needed in the DN reduction. We give the precise obstruction and then resolve this
example by using DN as well as NN. All calculations below concern
whole components and diagram maps.

Let N have area 012333 and strict edges 14,25. We use NN at f=25,
with q=23 and r=35. The unmarked corner 03 has fixed status on each
source component. There are two distinct connected seven-edge components

    C_69:  seed {01,02,12,13,14,23,25}, size 69,
    C_126: seed {01,02,03,12,13,14,25}, size 126.

The first omits 03 and the second selects it. Their source completion
under the standard NN middle and target-flip joins is exactly their
union. In particular the upper join associated with the target triangle
123 equates membership at the following representatives:

    {01,02,12,13,14,25,35} in C_69,
    {01,03,13,14,23,25,35} in C_126.

These are imposed joins for completing the NN image, not actual source
flips. They cannot be actual source connections, since a maximal corner's
selected status cannot change.

Both components contain a state acyclic after reversing the common
strict edges 14,25. Thus neither can be removed by an everywhere-redundant
strict corner or by the mixed-cycle deletion rule for those stricts.
Thus the standard completion at seven selected edges forces a surviving
addition; it cannot be made using inactive seven-edge additions alone.
This does not exclude corrections using different edge layers or further
RHS diamonds. Nor does it refute the recurrence or the saturated isolation
question.

There is also an induction trap to avoid. Deleting absent 03 from C_69
and marking its selected corner 02 gives its original DN representation
L of area 012233, strict 02,14,25. That identity map returns to the
original DN problem. It cannot by itself be counted as a completed DN
reduction. Conversely, marking 03 in C_126 gives the saturated diagram
with strict 03,14,25. The respective states

    {01,02,13,14,23,25,45} in C_69,
    {01,03,12,14,25,34,45} in C_126

remain mixed-acyclic with these native strict markings. The additional
markings do not supply an inactive-corner solution either.

### First apply DN to the smaller representation

In L there are eight normal edges. Its seven-edge layer has four
selected normals, so it has 70 states. It is exactly C_69 together with
the singleton component

    S={01,02,12,14,24,25,45}.

The DN target R has area 012332 and strict 03,14,35. Its seven-edge
layer likewise consists of a 69-state component D_69 and the singleton

    S'={01,03,13,14,34,35,45}.

These component assertions are verified by complete actual-flip checks
in the two fixed layers. A seed for D_69 is

    {01,02,03,12,13,14,35}.

The full DN layer goes to the full target layer. Indeed, for each
exterior selection the two middle states have equal edge counts, so
they occur together or neither occurs. Pair them by the diamond, use
the empty/full endpoint maps, and use the target diamond. The swap
preserves the number of exterior edges, and the result is exactly the
indicator of the target seven-edge layer.

The bottom endpoint swap 2<->3 takes S to S' on the entire selected
relation. It preserves the sink order: the isolated vertex 3 becomes
2 and the other sink remains 5. Subtracting this singleton identity from
the full-layer identity gives the complete DN recurrence

    X(C_69)=X(D_69),                    X=K,E.       (E1)

This uses the DN diagram identity and whole-component checks; it does
not appeal to the component expansion or to matching polynomial values.
The target has the same area as L and smaller moment, so (E1) is a
valid forward DN step in the induction order.

### Now finish the NN component bracket

Return to N and the NN target Y of area 012332, strict 14,35, with 03
unmarked. The component D_69 is still whole in Y: it selects the maximal
corner 03, so unmarking it changes no available flip.

Applying the proved NN construction to C_69+C_126 gives D_69 plus the
eight whole Y components in the table below. Each term has coefficient
one. The construction's coefficients agree across every actual target
flip; the fixed check verifies the entire target components, not only
their displayed seeds.

| Whole Y-component seed | Size |
| --- | ---: |
| 01,02,03,12,14,35 | 52 |
| 01,02,12,13,14,35 | 33 |
| 01,02,12,13,14,23,35 | 29 |
| 01,02,12,14,24,35 | 1 |
| 01,02,12,14,23,24,35 | 3 |
| 01,03,13,14,34,35 | 4 |
| 02,13,14,34,35,45 | 1 |
| 01,02,13,14,34,35,45 | 3 |

Use (E1) to cancel C_69 against D_69. We obtain

    X(C_126)=sum_(eight displayed components D) X(D),
                                                 X=K,E. (E2)

The sizes sum to 126. Every final diagram has fewer natural edges than
N. This is a complete NN collection for C_126, and (E1) handles the
empty-corner component which forced its addition. It illustrates why
using another recurrence can succeed when deleting inactive components
alone cannot.

### Endpoint attachments and the remaining scope

All swaps in (E1),(E2) exchange 2,3 and fix endpoints 0,5. Their diamonds
and redundant-edge identities preserve the endpoint-marked quantities.
Consequently the proved
[endpoint-attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#endpoint-attachment-theorem-completed-audit)
extends both identities to arbitrary chosen components attached at BOTH
ends, with no edges crossing between block interiors. No component
expansion for either attachment is assumed.

A fixed check attaches the two-state triangle component at each end.
After shifting the middle vertices by two, the three areas are

    DN source: 0121223312,
    NN source: 0121233312,
    common target: 0121233212.

All eleven products (the two terms of (E1), the source of (E2), and its
eight outputs) are complete actual components. Their sizes are 276 on
each side of (E1), and 504 on each side of (E2).

Related Rust: `dn_joint_span --nn-empty-completion` checks the two source
components, their exact completion class, the displayed forced join,
mixed-acyclic witnesses with both common and native strict markings,
the two 70-state DN layers and their singleton swap, all NN target
coefficients and component sets, and the eleven attached products.
It uses graph routines only, without polynomial or quotient calculations.
Frozen sources and receipts: `empty-nn-correction-20260929/` under the
external request folder.

The general NN collection problem is still open. We have not proved
that every forced extra component admits a suitable independent recurrence,
or that direct RHS diamonds always complete the image. The two identities
here resolve this particular empty-corner obstruction and extend under
the stated attachments; they are not an extrapolation to crossing exterior.

## Components on which the adjacent short is fixed

2026-09-29 continuation. We give a uniform whole-component reduction for
one class of NN inputs, with arbitrary exterior and no cycle-rank bound.
We use the same eligible geometry as above:

    w<x=w+1<z,     f=wz,     q=wx,     r=xz.

The source L has f strict and q,r normal. The only natural edge properly
containing r is f. The target R deletes f and marks r strict. The common
exterior is invariant under sigma=(w x), which fixes its strict edges.
We also put H=L-f-r, retaining only the common strict edges. Both deletions
are legal: r is a maximal natural edge after deleting f.

**Theorem.** If the selected status of q is constant on a whole source
component C, then C has a bijection with a whole component of a smaller
diagram, preserving both K and E. The possibilities are exactly:

| q | r | Map on each state A | Smaller diagram |
| --- | --- | --- | --- |
| absent | absent | sigma A | R |
| selected | absent | A-f | H |
| selected | selected | A-f | R |

In particular, a whole component cannot have q always absent and r
always selected. The theorem allows empty unmarked exterior corners;
we do not require saturation or a first-drop choice of this contact.
We prove the missing-sector assertion first, then the whole-component
claims in the table.

### A leftward path must introduce q

We use the following elementary observation about the actual flips.
If two selected covers ij and kj have i<k<j, then

    kj -> ik, retaining ij,                              (FQ1)

is actual. The edge ik is natural because it lies inside ij. It is
absent: otherwise ij would be bypassed through k. The cover of kj
ensures that ij still covers after the exchange; the cover of ij
ensures that there was no old i-to-k path. These are precisely the
cover conditions for (FQ1). The exchanged edges cannot be strict
corners, since both lie properly inside the natural edge ij.

For a selected state A set W(A)=sum_(ij in A)(i+j). Each move (FQ1)
strictly decreases W, by j-i. Thus successive leftward flips terminate.
At a terminal state, every vertex has at most one incoming cover.
Consequently the predecessors of any fixed vertex form a chain: follow
its unique incoming cover backwards, and use that every comparability
in a finite poset is a path of covers.

Now start with any source state selecting f,r and omitting q. Until q
first appears, f remains selected because it is strict, and r remains
selected because its only possible exchange is r->q retaining f.
Such a state cannot be terminal for leftward flips. Indeed w and x
both reach z, so the terminal chain property would make w reach x.
Since they are adjacent, this would require q itself.

We may therefore keep making (FQ1) until q appears. Strict decrease
of W proves termination, and every move stays in the actual component.
This proves, for NN and also for the DN geometry, that every state
selecting f,r lies in a component with a q-selected member. We do not
claim that the path keeps q selected, exposes f, or pairs the two
middle states with identical exterior. Those stronger conclusions do
not follow from this argument.

### The three whole-component maps

If q is fixed on C, then r is fixed too: every flip changing r changes
q. The preceding path excludes the constant 01 sector.

In sector 10, f must be redundant at every state. If it covered, the
adjacent q would also cover and the f-retained flip q->r would leave
that sector, contrary to constancy of q on the whole component.
The inactive-corner deletion theorem therefore identifies C exactly
with a whole component of L-f. Its newly exposed corner r is absent,
so deleting r gives the stated whole component of H.

In sector 11, q,r already bypass f. The same inactive-corner theorem
deletes f on the entire component. Marking the selected maximal r
changes no flip, giving a whole component of R.

For sector 00, relabel all selected edges by sigma. This gives actual
states of R. A source flip preserving q,r conjugates to a target flip
preserving q. Conversely every q-preserving target flip conjugates
back: a triangle containing both adjacent vertices would exchange q,
so no such triangle occurs among these flips. Relabeling the remaining
triangles preserves all their cover tests. Thus sigma C is connected
and closed under q-preserving flips, including all exterior flips.

We still have to exclude a target flip introducing q. There are two
forms, and we must exchange the roles of its other two selected edges
when pulling it back:

| Target flip introducing q | Source flip introducing q |
| --- | --- |
| tw -> q, retaining tx, t<w | tw -> q, retaining tx |
| xd -> q, retaining wd, x<d | xd -> q, retaining wd |

Although the displayed edge names agree, sigma interchanges the two
selected edges within each row. Both were covers in the target state,
so both are covers in the source state; the indicated source flip is
therefore actual. Its two non-q edges are natural and its exchanged
short is normal because it lies inside the selected long. Either row
would introduce q in C, a contradiction. There is no further form
of q-changing triangle. Thus sigma C has no exit and is a whole
target component, completing the table.

Corner deletion in sectors 10 and 11 preserves the full selected
closure. In sector 00, sigma is the usual NN endpoint map: w has its
outgoing edge f, so the adjacent interchange preserves sink order and
hence HRV fibre sizes. All three maps preserve K and E. Their target
natural areas are smaller by two, one and one edges, respectively
in the order of sectors 10, 11 and 00. We have proved a component
recurrence, rather than only an equality of total diagram sums.

### Scope and checks

This removes all components with fixed q from the general NN question.
The remaining components contain both q-selected and q-absent states.
The leftward argument supplies a path introducing q but does
not collect the signed output terms there. In particular it does not
resolve the 84-state or the coupled 69/126 examples uniformly.

Related Rust: the existing external `dn_joint_span --nn-fixed-short`
uses only the actual graph routines in `component_source_probe.rs` and
`nn_component_transport::components`. It checks each complete image
against the full target component, not just flips inside its stratum.
It also constructs the decreasing leftward path from every q-absent,
r-selected state in the fixed diagrams. No polynomial calculation is
called. The NN fixtures are the same five as in the preceding middle
slice check; six DN fixtures check the consequence below. Frozen
sources, commands and counts are in `fixed-short-20260929/` under the
project's external request directory. These checks support the general
proof above; their finite range is not used to infer the theorem.

## When the terminal short is fixed

2026-09-29 continuation. We now allow q to vary on C. We prove two
further whole-component reductions, using actual cover-preserving paths
and then the ordinary inactive-corner identity. We retain the preceding
NN notation f=wz, q=wx, r=xz with x=w+1. The first reduction also
applies directly to DN.

**Theorem.** If r is selected throughout a whole source component C,
then f is redundant throughout C. Consequently deleting f identifies C
with one whole component of L-f, and marking its selected corner r gives
a whole component of the NN target R. Both K and E are preserved.

Here q can change arbitrarily, and exterior edges can cross the displayed
triangle. We do not assume a bound on cycle rank or any exposure condition
on the other strict corners.

### Expose r while keeping f a cover

Suppose instead that A in C has f covering. Then q is absent, since
q,r would bypass f. Process all selected edges vz with x<v<z in
DECREASING order of v, performing

    vz -> wv, retaining f.                              (FR1)

Each move is actual. At the stage for v, any bypass of vz would end
in uz with u>v. All such selected incoming edges have already been
removed. The newly added edges start at w<v, so no path from v can
use them. Thus vz covers. The retained f covers initially and remains
a cover after each actual f-retained flip; its cover also ensures that
wv is absent before the move. Both exchanged shorts lie properly
inside f and therefore are natural and normal.

After this sweep the only selected edges into z are f and r. Indeed
any natural tz with t<w would properly contain the maximal f, and
there is no vertex strictly between w and x. The edge r now covers:
a path from x cannot reach the earlier vertex w, so it has no alternate
way to enter z. We finish with the actual flip

    r -> q, retaining f.                               (FR2)

This gives an r-absent member of C, contradicting the hypothesis.
The contradiction proves the theorem. The path has at most z-x moves
and retains every strict edge. Its purpose is to change the status
of r; it does not claim to restore the exterior at its endpoint.

In particular, an f-active component which has any r-selected member
must have BOTH r statuses. Conversely, any component with both r
statuses is f-active, since a flip changing r must retain f as a cover.
The possibility of an f-active component with r always absent is a
separate question; the first theorem does not rule it out.

### The absent-r case when w is least in its selected block

**Lemma.** Suppose f covers in A, r is absent, and w,x belong to the
same selected weak block, whose least vertex is w. Then an actual path
from A introduces r while keeping f a cover at every step.

If q is present, use q->r retaining f immediately. Otherwise, first
process the selected edges wv, x<v<z, in INCREASING order of v, using

    wv -> vz, retaining f.                              (FR3)

At the stage for v there is no smaller selected outgoing edge at w:
q is absent and all earlier ones have been removed. Hence wv covers.
The inserted edges end at z and cannot create a new path from w to v.
The covering f excludes a selected vz. Thus each move is actual and
keeps f covering. No such move introduces r.

The vertex w now has only its selected edge f. It has no incoming
selected edge because it is least in its weak block, and f's maximality
excludes natural outgoing edges beyond z. Deleting this pendant vertex
leaves the rest of that selected block connected, with least vertex x.
Normalize this rest by the leftward cover flips (FQ1), never using w.
The finite endpoint-label sum decreases, so this terminates. At the
terminal state each vertex has at most one incoming cover. Its connected
Hasse graph is therefore a directed tree rooted at its least vertex x;
in particular x reaches z. Hasse edges and selected edges have the same
weak blocks, since every selected comparability is a path of covers.

Every normalizing flip is also actual in the full source. The pendant
w cannot occur inside a path between other vertices, and f keeps covering
because it is still w's sole outgoing edge. The edge r stays absent:
its only possible exchange uses f and therefore w.

We next use the same incoming cut as the earlier exposure argument.
In this prepared state let

    I={v : x<v<z, vz is selected, and x reaches v}.

This set is nonempty because x reaches z and r is absent. Apply (FR1)
only to I, again in decreasing order. A bypass of the currently processed
vz would end in uz with u>v reachable from x, so u would belong to I
and its incoming edge would already have been removed. New edges starting
at w cannot change paths starting at x or v. Thus all cut moves are
actual and retain the covering f.

After the cut, x no longer reaches z. Put p=min I. The last move
inserted the covering edge wp, while x still reaches p: no edge ending
below z was removed. Choose the last cover tp on a cover path from
x to p. The two covers wp,tp permit

    tp -> wt, retaining wp.                             (FR4)

Here x<=t<p, and the new wt is a cover. This move also preserves
coverhood of f. Any new bypass would have to start with the newly
inserted wt, but t is reachable from x and x does not reach z.
Removing tp cannot create a t-to-z path, and an edge starting at w<t
cannot create one either. The x-to-t prefix survives the exchange,
and x still does not reach z.

Replace p by t and repeat. This strictly decreases p until t=x,
when the new edge is q. The edge f still covers, so the actual flip
q->r retaining f finishes the path. All exchanged edges in the cut
and in (FR4) are properly contained in selected natural longs. The
normalization step likewise exchanges only normal shorts. Thus every
original strict decoration and every exterior edge not explicitly
changed by these moves remains valid. This proves the lemma.

**Whole-component consequence.** Suppose r is absent throughout C,
q varies on C, and w is least in its selected weak block. Since q
occurs somewhere, x belongs to that same invariant block. If f covered
in any member, the lemma would introduce r, a contradiction. Therefore
f is redundant everywhere. Deleting f and then the absent maximal r
identifies C with one whole component of H=L-f-r, preserving K and E.
This decreases natural area by two.

In particular, at a leftmost NN contact w=0, every component with
constant r is now reduced: use this result when q varies, and the
preceding fixed-q theorem otherwise. This is not a proof of the
NN step for components where both short edges vary.

### Remaining boundary and verification

For a general contact, the second argument needs the stated least-vertex
hypothesis. An incoming selected edge at w prevents (FR3) from making w
pendant; simply ignoring that edge would invalidate the subsequent
normalization. We have not proved that all constant-absent-r components
with variable q are inactive at f. The fixed examples satisfy that
stronger statement, but their finite checks are not a general proof.
Nor do either of these reductions collect the main two-variable sector.

Related Rust: `dn_joint_span --nn-fixed-r` constructs the paths above
using the existing cover/flip oracle, and checks the component label,
strict edges, selected-edge count and coverhood of f at EVERY move.
It uses `Graph::neighbors` for the selected weak block and
`Poset::order_ideal_generated_by` for reachability. It also checks each
claimed deletion image against a complete component computed in the
smaller diagram. No polynomial or component-expansion theorem is used.
The five NN and six DN fixtures give 5132 paths with 8346 checked flips.
All 681 claimed inactive-component images are whole; 146 of these
components have variable q and were outside the preceding fixed-q class.
Frozen sources, commands and receipts are in `fixed-r-20260929/` under
the project's external request directory.

## Removing the least-vertex restriction

2026-09-29 continuation. We now prove the absent-r reduction with arbitrary
incoming exterior, including the DN geometry. The least-vertex condition
in the preceding section is no longer needed. We first establish the
simple path normalization used in its place.

### Making one vertex reach another inside a component

**Reachability lemma.** In an ordinary decorated natural diagram, let
u<v belong to the same selected weak block of a state A. There is an
actual-flip path from A to a state in which u reaches v. All prescribed
strict corners remain selected. If v=u+1, the endpoint selects uv.

Take an undirected path from u to v in the Hasse graph of A. Such a
path exists because replacing each selected edge by a path of covers
preserves the weak blocks. Let [a,b] be the smallest label interval
containing the chosen path.

If b>v, the vertex b is internal to the path and has two neighbors
i<j<b. The two incoming covers ib,jb give the actual flip

    jb -> ij, retaining ib.

Shortcut the old segment i-b-j by the selected ij. All edges of the
shortened path remain selected and have endpoints in [a,b-1]. They
need not remain covers, but each can be replaced by a cover path inside
its own endpoint interval, since all edges point forward. We thus
obtain a Hasse walk, and then a path, entirely in [a,b-1].

If a<u instead, the two neighbors of the internal minimum a are
a<i<j. Use the outgoing-cover flip ai->ij retaining aj, and the same
shortcut and cover refinement gives a path in [a+1,b]. Each step
strictly shortens the containing interval. The exchanged shorts are
normal: they lie properly inside the retained natural long. We finish
with a Hasse path from u to v inside [u,v].

Now perform leftward cover flips inside [u,v] until none remains.
Their finite endpoint-label sum decreases. Cover tests inside this
interval are the full cover tests: a forward path between its vertices
cannot leave it and return. These flips preserve the weak blocks of
the selected graph induced on [u,v]. At termination every vertex has
at most one incoming cover. Each connected Hasse component is an
increasing directed tree rooted at its least vertex. The component
containing u and v has least vertex u, so u reaches v. This proves
the lemma, including arbitrary fixed exterior.

Consequently, if an adjacent edge is absent throughout a whole component,
its endpoints lie in different selected weak blocks. This conclusion is
about a single adjacent edge; the argument does not simultaneously make
all pairs comparable.

### Normalize away from w even when edges enter w

Suppose f=wz covers in A, r=xz is absent, and w,x lie in the same
selected weak block. As before x=w+1. We claim that a path introduces
r and keeps f covering throughout, without assuming that w is least.

If q is selected, the f-retained flip q->r already does this. Otherwise
apply the outgoing sweep (FR3): replace selected wv, x<v<z, by vz in
increasing order of v, retaining f. Its proof used only outgoing paths
from w, so incoming selected edges do not affect it. We reach a state
where f is the ONLY outgoing edge at w. Incoming edges tw may remain.

Consider the selected graph with w removed, leaving its incident edges
unchanged in the full state while we make flips on the other vertices.
The induced natural graph is interval-closed in the remaining order,
and its surviving strict corners are still maximal.
These flips lift exactly to the original graph. Indeed an alternate
path between other vertices which visits w must leave it along f.
It could bypass a tested natural edge only if that edge properly
contained f, contradicting maximality of f. Thus the cover tests agree.
All these flips also keep f covering, because it stays w's only
outgoing edge. They preserve the weak blocks of the graph with w removed.
The absent r is a maximal natural edge of that graph and stays absent.

Let B be the weak block containing x in this graph with w removed.
There are two cases, neither requiring a least-vertex assumption.

**The block B contains z.** Apply the reachability lemma to x<z in
the graph with w removed. We obtain x-to-z reachability while f still
covers and r remains absent. Now use the incoming cut and descending
cover forks (FR4) from the preceding section: remove, in decreasing
order, the selected vz whose tail v is reachable from x, replacing
them by wv while retaining f. This clears x-to-z reachability and
leaves a covering wp with x reaching p. The cover-fork descent decreases
p to x, introducing q without losing the cover of f. Finish with
q->r retaining f. Those cut and fork proofs do not use an assumption
on incoming edges at w.

**The block B does not contain z.** Since x and w were weakly connected
in the full state, some selected incoming tw has t in B. The only
other kind of edge incident to w is f, whose endpoint z is outside B.
In particular t<w<x. Apply the reachability lemma in the graph with
w removed to make t reach x. This keeps tw selected, keeps f covering,
and preserves the separation of B from z. Thus x still does not reach z.

The selected tw and the increasing t-to-x path now put w,x in the
same weak block of the graph induced on vertices at most x. Apply the
adjacent case of the reachability lemma there, stopping when q appears.
Every flip lifts to the full graph, since cover tests ending at or
below x use only vertices at or below x.

Until q appears, w still has f as its only outgoing edge. Moreover none
of these lower flips can change a path starting at x: every changed
edge has tail strictly below x and head at most x. Hence x still does
not reach z after q appears. Adding q therefore does not bypass f.
The final flip q->r retaining f is actual. This proves the claim in
both cases and retains every strict decoration throughout.

### Whole-component conclusion for both recurrences

**Theorem.** Let C be a whole NN or DN source component. Suppose r is
absent throughout C and q varies on C. Then f is redundant throughout C.
Deleting f and then the absent maximal r identifies C with ONE whole
component of L-f-r, preserving K and E and decreasing natural area by two.

Since q appears somewhere in C, its endpoints w,x belong to the same
invariant selected weak block. If f covered in any member, the preceding
construction would introduce r inside C, contradicting its constant
absence. Thus the inactive-corner deletion and absent-corner identity
apply to the entire component, proving the theorem.

Together with the preceding selected-r theorem, every component with
fixed r and variable q is now reduced, with no incoming-edge exception.
The fixed-q theorem covers the other fixed-r components. Thus every
component still requiring general NN/DN collection has BOTH q and r
varying. Such a component is f-active because every flip changing r
retains f as a cover. This is a proved reduction to that remaining case,
not a proof that its paired middle states share the same exterior or
that its initial image is already a union of whole RHS components.

### Verification

Related Rust: `dn_joint_span --nn-fixed-r-general` extends the same
external consumer, using the existing cover/flip model and maintained
Graph/Poset APIs. The new path constructor selects cover paths, removes
their extreme vertices, and then performs the stated leftward flips;
it does not search the full component for a desired endpoint. A complete
component index is used only to verify each resulting move's membership.
The checks verify strict edges, edge count and coverhood of f at every
step, and compare every claimed corner-deletion image to a whole smaller
component. Both upper and lower path-shortening cases occur, as do both
cases for the block B, including DN states with selected e=uw.

The separate `--reachability-activation` check tests the path lemma for
every same-block ordered pair in three fixed diagrams, including an
empty unmarked corner. No polynomial calculation, Lean build or new
worker is involved. Frozen sources, commands, counts and receipts are
under `general-fixed-r-20260929/` in the external project request folder.

## Pairing the middle states when joint selection is absent

2026-09-29 continuation. We retain f=wz, q=wx, r=xz and x=w+1.
We call an edge a bridge when deleting it disconnects its endpoints in
the undirected selected graph. This is stronger than being a cover.
The following argument uses the preceding reachability lemma and actual
flips only. It applies to both NN and DN, with arbitrary exterior.

### Introducing q while keeping r

**Lemma.** Suppose A selects f,r and omits q. If either f or r is
not a bridge of A, an actual path introduces q while keeping r selected.
Every prescribed strict corner stays selected.

First suppose f is not a bridge. In A-f, the vertices w,z are in
the same weak block; the selected r puts x in that block too. Apply
the adjacent reachability lemma to w,x in D=L-f. This introduces q.
The edge r is maximal in D and therefore cannot be exchanged by these
flips. Every flip lifts after inserting f: an alternate directed path
using maximal f could not bypass any other natural edge. Thus we have
the required path with f,r retained.

Now suppose f is a bridge and r is not. Deleting f does not destroy
a cycle through r, so x,z are weakly connected in A-f-r. The two
successive corner deletions give the ordinary diagram H=L-f-r.
Apply the reachability lemma in H to make x reach z. Lift this path
by inserting r and then f. The first insertion preserves all other
cover tests because r is maximal in D; the second does so because f
is maximal in L. The selected weak block of w stays separate from
the block containing x,z in D. Consequently f stays a bridge, hence
a cover, throughout this preparation. We have produced a directed
x-to-z path avoiding r.

Let I consist of the selected incoming tails v with x<v<z which
are reachable from x. The set I is nonempty. In decreasing order of
v, perform vz->wv retaining f. These are the same incoming-cut moves
as before: a bypass of the current vz would end in a larger incoming
tail already removed. The extra selected r cannot occur in a path
starting at v>x. Every cut move therefore retains a covering f.

After the cut x no longer reaches z without r. The last inserted wp,
where p=min I, covers, and x still reaches p. Choose a last cover tp
on an x-to-p path and perform tp->wt retaining wp. Repeat with p=t.
The strictly decreasing p eventually reaches x and introduces q.
All these cover tests end below z, so retaining r does not change
them. Until the last move, f still covers: any new bypass would begin
with wt for t>x, but no such t reachable from x can reach z without
r, and it cannot use the earlier tail x of r. On the final move f
becomes redundant through q,r. That is allowed: this last flip retains
wp, not f. We have kept r selected throughout and proved the lemma.

### A component consequence and its precise scope

**Theorem.** Let C be a whole source component containing no state
which selects both q and r. In every r-selected state of C, both
f and r are bridges. Hence its same-exterior middle mate belongs to C:

    Q+f+r in C  implies  Q+f+q in C.                  (JS1)

Otherwise the lemma would produce a forbidden jointly selected state
inside C. Since both displayed arms are bridges, deleting them leaves
w,x,z in three different weak blocks. In particular f,r are covers,
and their single actual root flip proves (JS1), restoring exactly Q.
The paired state also has f,q as bridges.

Thus h01(Q)<=h10(Q) for every exterior Q in this class of components.
The NN split (2) has only nonnegative coefficients: its only possible
negative coefficient was h10-h01. In fact every coefficient is zero or
one. The two summands in h00+h01 have different selected-edge counts,
whereas one component has fixed edge count; and h11 is zero here.
We have therefore transported C to a set of smaller-diagram states
using paired diamonds, endpoint swaps and redundant-f deletion.

This is not yet a whole-component recurrence. It proves the direction
(JS1), not the reverse for every 10 state. Any unmatched 10 state has
redundant f by the original exposure argument. Nor have we proved that
f is a bridge at every 00 or 10 state of C. These stronger assertions
must not be inferred from the finite examples.

### The remaining output boundary is real

Even the nonnegative image above can omit a neighbor in the target.
Take the NN source with area 01232, f=24, w=2, x=3, z=4, and no other
strict edge. The component with seed {01,02,03,24} has eleven states,
has both short edges varying, and never selects them jointly.
In D=L-f, the initial image gives

    {03,12,13,34} coefficient 0,
    {03,13,23,34} coefficient 1.

These states are adjacent by the actual flip 12->23 retaining 13.
So pairing the middle states and obtaining a nonnegative image does
not by itself finish the output component. This example has an unmarked
maximal corner 03; it does not contradict the tree theorem's saturated
eligible-source hypothesis. Additional diamonds or another permitted
recurrence are still needed to complete these output pieces.

Related Rust: graph-only `dn_joint_span --nn-joint-shorts` constructs
both paths in the lemma, replays every step through the actual-flip
oracle, and checks component membership, strict edges, edge count and
retention of r. It separately checks (JS1), both bridges and the three
exterior weak blocks for every applicable component in five NN and six
DN fixtures. It checks the zero-or-one NN coefficient vector against
every complete target component, including the displayed failed
boundary. These are graph and indicator calculations, not polynomial
or basis calculations. Frozen sources and receipts are in the external
`joint-shorts-20260929/` directory.

## Full-layer recurrence for arbitrary source trees

2026-09-29 continuation. We now resolve the preceding eleven-state
example by a uniform whole-component recurrence for source trees.
The source need not be saturated. This supplies a diagram recurrence;
the forest-component expansion itself was already proved by
[connected aggregate extraction](COMPONENT_CONNECTED_AGGREGATE.md).
We do not use that expansion here.

Write F_m(D) for all states of D with m selected edges, including its
strict edges. It is always a union of whole components. The NN
diamonds and endpoint identifications give, for X=K,E,

    X(F_m(L)) = X(F_m(R)) + X(F_(m-1)(R)).             (TL1)

Indeed, put b=|Q|, counting all exterior selected edges. The full-layer
indicator has h00=[b+1=m], h10=h01=[b+2=m], and h11=[b+3=m].
Its unmatched middle residual vanishes. The two target coefficients
in (2) are exactly the indicators of target edge count m or m-1.
This proves (TL1) directly from diagrams and already groups the output
into whole components.

### Reordering disconnected blocks gives a smaller whole component

We use the following reduction also for cyclic correction components.
Suppose the natural graph of L is connected, and D is a disconnected
selected component. Its selected weak partition pi is fixed. Order the
blocks by their least vertices, order the vertices increasingly inside
each block, and concatenate the induced natural diagrams L|B.
Call the resulting ordinary diagram L_pi.

No selected edge crosses pi. Every actual flip has its three vertices
in a single selected block, and its cover tests use only that block.
Consequently the blockwise increasing relabeling identifies D, with
its ENTIRE flip graph, with one whole component D_pi of L_pi.
All original strict edges lie inside blocks, since they are selected;
their restrictions remain maximal natural edges. The induced graphs
are interval-closed in their induced orders, so L_pi is valid.

The map preserves K by relabeling vertices, and preserves E because
reachability and the order of reachable vertices inside each block
are unchanged. Every HRV fiber lies inside a block. We therefore have

    X(D)=X(D_pi),  X=K,E.                             (TL2)

The natural edges of L_pi are exactly the original natural edges
internal to blocks. Connectedness of the natural graph and the presence
of more than one block imply that at least one natural edge was removed.
Thus L_pi has the same vertex count and STRICTLY smaller natural area.
This is a whole smaller component, not just an uncollected product.
We do not assume an expansion for its factors, which may contain cycles.

### Isolating the full-envelope tree component

Let C be a connected source tree component whose selected envelope is
the full natural graph of L, and put m=n-1. By
[tree connectivity](COMPONENT_TREE_CONNECTIVITY.md#trees-with-a-fixed-envelope-are-connected),
C consists of all connected trees with that envelope. No assumption
that every maximal natural edge is marked strict is needed.

Take every other component D in F_m(L), once each, and form a smaller
component B_D as follows.

* If D is disconnected, use D_pi in (TL2).
* If D is connected, it is a tree, because it has n-1 edges. Its
  envelope must be proper, by the tree-connectivity theorem. Choose
  an absent maximal natural edge g of L. It is normal, and is absent
  throughout D. Deleting g identifies D with one whole component
  B_D in L-g. Selected relations and all actual flips are unchanged.

Both constructions preserve K and E and strictly decrease natural
area. Subtract these independent whole components from (TL1). We obtain

    X(C) = X(F_(n-1)(R)) + X(F_(n-2)(R))
           - sum_(D in F_(n-1)(L), D != C) X(B_D).    (TL3)

Every term on the right is now a whole component or an explicitly
specified union of whole components in a smaller ordinary diagram.
The NN target decreases area by one, as usual. This is the desired
signed component recurrence for this entire class. It uses the full
source layer as a convenient completion, and proves why EVERY added
component has an independent smaller-diagram reduction.

If a connected source tree has proper envelope to begin with, delete
an absent maximal natural edge directly. A disconnected forest already
splits into its blockwise components, and (TL2) applies whenever the
ambient natural graph is connected. Thus no new NN middle comparison
is needed for forest components, including unsaturated source diagrams.

### The eleven-state boundary example and the limit of the argument

For area 01232 with strict 24, the source tree component seeded by
{01,02,03,24} has full envelope. The layers F_4(R) and F_3(R) together
give 20 whole target components with 35 states. The other source-layer
components comprise four smaller-envelope tree components with 13 states
and seven disconnected components with 11 states. Equation (TL3) gives
the complete recurrence with state counts 11=35-13-11. Each of those
eleven corrections is mapped to its own whole smaller component.
This resolves the example's recurrence; it does not assert that the
original unmodified zero-or-one image was whole or that all corrections
lie in the main target R alone.

For a connected cyclic C, the same layer can contain another connected
cyclic component with the full envelope. Neither case in the subtraction
argument then applies automatically. We have not proved a general
uniqueness statement or reduced all such additional components. This
remains the essential limitation of the full-layer method.

Related Rust: graph-only `dn_joint_span --forest-layers` checks the
full-layer coefficients, the unique full-envelope tree component,
every smaller correction image and BOTH directions of its actual flip
graph. It verifies validity and strict decorations of the reordered
block diagrams and the strict decrease of every final diagram.
Five NN and six DN fixtures are checked; the DN formula is recorded
in the companion note. Frozen sources, commands and receipts are in
the external `forest-layers-20260929/` directory.

## The largest edge layer in which a corner can cover

2026-09-29 continuation. We now give a whole-component recurrence for
a uniform cyclic class, without assuming general active-component
uniqueness. The source need not be saturated, and the exterior is arbitrary.

Let f=wz be a strict maximal natural edge, let d=z-w>=2, and let
N be the number of natural edges. Put k*=N-d+1. A component is
f-active if f covers in at least one of its states.

**Theorem.** Every component with more than k* selected edges is
inactive at f. At exactly k* selected edges there is exactly ONE
f-active component C*. All its f-covering states form an explicit
path of d states. Every other component in that layer deletes f to
one whole smaller component.

### The covering states are a chain of cuts

For every w<i<z, at least one of wi,iz must be absent if f covers.
These d-1 pairs of edges are disjoint, so at least d-1 natural edges
are absent. This proves the upper bound k*.

At equality, exactly one edge of each pair is absent, and EVERY other
natural edge is selected. Write T for the intermediate vertices with
wi absent and iz selected, and S for those with wi selected and iz
absent. If i in S precedes j in T, the selected edges wi,ij,jz
bypass f. The middle edge ij is selected because it belongs to none
of the arm pairs. Thus every vertex of T precedes every vertex of S.

The covering states are therefore precisely

    A_p = G - {wi : w<i<=p} - {iz : p<i<z},
          w<=p<z,                                    (DL1)

where G denotes the full selected natural edge set. Conversely f
covers in each A_p: an increasing path leaving w without f starts
above p, whereas an increasing path entering z without f ends at or
below p. It cannot do both. Such a path cannot leave [w,z] and return.
Every state (DL1) retains all strict decorations, since every omitted
edge lies properly inside the maximal f.

For w<=p<z-1, the actual flip

    w(p+1) -> (p+1)z, retaining f,                    (DL2)

takes A_p to A_(p+1). The retained f covers, and w(p+1) covers
because w has no selected outgoing edge with a smaller intermediate
head. Thus all d covering states lie in one actual component C*.
Every f-active component of this layer contains one of these states,
so C* is unique. All other components have f redundant throughout;
the established inactive-corner deletion identifies each with one
whole component of L-f. This proves the theorem.

In an eligible NN or DN source, q=wx with x=w+1 and r=xz. The first
two states of (DL1) differ by q->r, so BOTH short edges vary on C*.
Thus this result directly handles a class of the remaining two-variable
cases. It does not follow merely from a fixed-short reduction.

### The complete NN recurrence and its cancellations

Let R be the NN target and D0=L-f, with r normal in D0 and strict
in R. Apply (TL1) at k=k* and subtract the other source components.
For both X=K,E we obtain

    X(C*) = X(F_k(R)) + X(F_(k-1)(R))
            - sum_(D in F_k(L), D != C*) X(D-f).     (DL3)

The theorem proves independently that EVERY subtracted image is a
whole component of D0. Both R and D0 have natural area N-1, so all
terms decrease the original induction order. Every component above
this layer already reduces by the same inactive-f deletion.

There is a useful exact cancellation in (DL3). A subtracted component
has k-1 edges. If it selects r, it is also one whole component of R
and cancels its copy in F_(k-1)(R). Distinct source components have
distinct deletion images, so no term is cancelled twice. What remains
has coefficients +1 on whole R components and -1 on whole r-absent
components of D0. The F_k(R) terms are unaffected. This collects the
whole output, rather than only checking individual middle terms.

This class has unbounded cycle rank. For the complete natural graph
on n vertices with only strict f=0(n-1), we have
k*=binomial(n-1,2)+1. The component C* is connected, and its cycle
rank is (n-2)(n-3)/2. Formula (DL3) holds for every n>=3. No expansion
for C*, its corrections, or any other cyclic component is assumed.

### Scope and checks

The proof uses equality in the missing-edge bound. Below k* there
can be extra absent edges not accounted for by the d-1 arm pairs;
the cut classification (DL1) then does not apply. The theorem does
not establish uniqueness of active components in arbitrary layers.
General NN/DN collection in those lower cyclic layers remains open.

Related Rust: graph-only `dn_joint_span --dense-recurrences` checks
the bound against every f-covering state in five NN and six DN fixtures,
checks the complete list (DL1) and every flip (DL2), and verifies each
inactive deletion image with BOTH directions of its actual flip graph.
It checks all cancellations against complete target components and
the decrease of every final diagram. The companion DN formula is
recorded in its note. Frozen sources and receipts are in the external
`dense-corner-layers-20260929/` directory.

A separate bounded activity scan is recorded in the same receipt.
It finds no duplicate connected active component at one edge count
in 148 saturated diagrams on 7--9 vertices without articulation and
with at most 18 natural edges (1,274,304 selected states). The fixed
articulation control reproduces its two different active components.
This is evidence for the older refinement, not its proof and not an
input to (DL1)--(DL3). In particular we do not use it to subtract an
unproved extra cyclic component in a lower layer.

## The largest layer with all corners covering simultaneously

2026-09-29 continuation. We sharpen the preceding one-corner bound by
using all maximal natural edges together. We prove actual flip paths,
then isolate one WHOLE component using the four diagram recurrences.
No component-expansion theorem or basis calculation enters the argument.

Let G be the natural edge set of an ordinary diagram L, and let M be
its full set of maximal natural edges, including any unmarked corners.
The original strict set is a subset of M. A selected corner cannot be
exchanged as a short edge, so its selection is constant on a component.
Marking an already selected maximal corner strict changes neither that
component nor its state contributions.

### Pair the two shorts of every corner

For each ac in M and a<b<c, link the two nonmaximal natural edges

    (ab) -> (bc).

These links form disjoint directed paths on G\M, with isolated edges
counted as one-node paths. Indeed, maximal intervals have distinct
left endpoints and distinct right endpoints. Thus a node ab has at
most one successor, from the corner starting at a, and at most one
predecessor, from the corner ending at b. Both endpoints strictly
increase along every link, so there is no directed cycle.

Write l_1,...,l_t for the numbers of nodes in these paths, and put

    m* = |M| + sum_j ceil(l_j/2).                       (JC1)

If a state selects every corner and all those corners cover, it cannot
select both shorts of any link. On each path its selected nodes are
therefore nonadjacent. It has at most m* selected edges. At equality,
each path has its maximum possible number of selected nodes.

Choose the last node of each path, then every second node backwards,
and add all corners M. Call the resulting state A*. Its edge count is
m*, and it retains every original strict edge. All corners cover in A*.
To prove the last assertion, suppose a corner uv has a selected bypass
starting u->b. The entire bypass uses nonmaximal edges: no other
maximal interval can lie inside uv. Since ub is selected, its successor
bv is absent. In A* every absent node has a selected successor. Hence
vt is selected for a corner bt with t>v. The remaining bypass b->...->v,
followed by vt, bypasses that corner bt. Repeating strictly increases
the corner head, an impossibility in the finite vertex order.

### Connect the maximum states by actual flips

**Theorem.** All m*-edge states selecting M with every corner covering
are in one whole actual component C*. They connect to A* by flips
retaining maximal corners and keeping every corner covering throughout.
This holds with arbitrary exterior edges and with unmarked corners.

We first describe the choices on one auxiliary path. On 2h+1 nodes
there is just one maximum selection, the odd positions. On 2h nodes,
every maximum selection has the form

    {1,3,...,2j-1} union {2j+2,2j+4,...,2h},
    0<=j<=h.

The final alternating selection is j=0. For j>0 there is exactly one
forward exchange preserving nonadjacency: move 2j-1 to 2j. Its next
available exchange, if any, is strictly farther left on that path.
Call such exchanges available before checking the actual cover tests.
Every available exchange has the form

    ab -> bc, retaining the maximal corner ac.        (JC2)

Order these exchanges by larger c first and, for equal c, smaller b
first. This tie-break is needed even for a single complete interval.
Choose the first available exchange. After making it, every remaining
available exchange is strictly later in this order. Other auxiliary
paths are unchanged. On the changed path the next exchange moves left,
and therefore has smaller corner head. A pair (c,b) determines at most
one exchange, because at most one maximal corner ends at c.

Let A be a state in the theorem and A' its proposed exchange. We show
that every corner still covers in A'. If a corner uv loses its cover,
its new bypass must use the inserted bc. In particular v>=c. If v=c,
the corner is ac, and its bypass begins a->d with d<b: it reaches b
before using bc, and ab has just been removed. Thus its first short
pair would have priority ahead of (JC2). If v>c, every exchange at uv
already has priority ahead of (JC2).

Follow such a bypass from its first edge ud. The paired node dv is
absent by nonadjacency. If dv has no selected successor, ud->dv is
an available exchange. Otherwise that successor is vt for a maximal
corner dt, and the suffix d->...->v->t bypasses dt with larger head.
Repeat. The corner heads strictly increase, so this process must end
at an available exchange. Its priority is ahead of (JC2), either by
the initial same-head comparison d<b or by a larger head. This
contradicts the preceding description of ALL available exchanges in
A'. Therefore no corner loses its cover.

The removed ab also covers in A. Otherwise its alternate a-to-b path
would survive its removal, since it ends below c; with the inserted
bc it would bypass ac in A'. We have just proved that ac covers there.
Thus ac and ab are covers in A, so (JC2) is an actual permitted flip.
Both shorts are nonmaximal and hence normal, regardless of the original
strict decorations. No original strict edge moves.

Repeat until all paths have their final alternating selection. The
available priorities strictly decrease, and at most sum_j floor(l_j/2)
flips are needed. The endpoint is A*. This proves the theorem, including
existence and uniqueness of the WHOLE component containing such states.
We do not claim that the all-cover states exhaust C*.

### Reduce every other component, then apply NN

We recall the proved
[alternating corner-deletion recurrence](COMPONENT_CORNER_DIFFERENCES.md#a-signed-recurrence-in-whole-smaller-components).
For a component D selecting M but having no state in which all M cover,
mark M strict. For nonempty T contained in M, deleting T partitions
D\T into whole components P_T(D) of the smaller diagram. Then, for
both X=K,E with the SAME signs,

    X(D) = sum_(nonempty T contained in M) (-1)^(|T|+1)
                 sum_(B in P_T(D)) X(B).              (JC3)

This does not assume the expansion. Deletion removes exactly the flips
retaining deleted corners, so every image part is whole. In each state,
a redundant corner has a bypass containing no other maximal corner.
That bypass survives every other corner deletion, and pairing deletion
subsets with and without this corner cancels the alternating state sum.
The redundant corner may depend on the state.

For EVERY other component D in the m*-edge source layer, choose its
smaller expression B(D) as follows. If some corner is absent, delete
that corner; D itself becomes one whole component of the smaller
diagram. Otherwise use (JC3). The theorem guarantees its hypothesis:
only C* contains a state in which all corners cover simultaneously.
All resulting diagrams lose at least one natural edge. Exactly the
same reductions apply to every component in every layer above m*.

For an eligible NN source let R be its usual target. The full-layer
identity (TL1), proved by the paired diamonds and endpoint maps, gives

    X(C*) = X(F_(m*)(R)) + X(F_(m*-1)(R))
              - sum_(D in F_(m*)(L), D != C*) B_X(D). (JC4)

Here B_X(D) means the valuation of the explicit whole-component
expression just constructed. After expanding (JC3), its sign in (JC4)
is (-1)^|T|. Every term is a WHOLE component of a strictly smaller
diagram. The main target loses one natural edge; the correction diagrams
lose the chosen absent corner or the nonempty set T. This proves the
complete signed NN recurrence at m*, with arbitrary crossing exterior.
The companion DN note gives the same construction with one target layer.

### New cases, verification and remaining limit

For the source area 012333, the auxiliary paths have lengths 3,3,3,
so m*=9. The 77-state NN component in that layer now has a complete
recurrence: the two actual target layers contain 120 states; eleven
missing-corner components account for 36 states and five alternating
correction components account for seven. The latter yield 35 whole
smaller terms. The earlier one-corner threshold was ten.

For area 0123434, m*=12 instead of the earlier one-corner threshold
fourteen. Its 2305-state NN component now has a complete recurrence.
The remaining 220 source-layer components have 698 states and reduce
by (JC3). These examples do not restrict the uniform theorem's size
or exterior. The DN nine-vertex example in the companion note lies
still farther below its old one-corner threshold.

Related Rust: the external graph-only consumer `dn_joint_span` checks
`corner_short_paths`, `normalize_max_corner_state` and every whole
correction image in mode `--corner-capacity`. It tests 14 NN/DN diagrams,
including empty unmarked corners and incoming attachments. The separate
`--corner-normalization-scan` checks the explicit paths in 148 saturated
diagrams on 7--9 vertices, with at most 18 natural edges. It enumerates
all source states to check the bound and uses the actual flip oracle
to verify each prescribed path; it does not search for the path.
Frozen sources, logs and commands are in the external
`joint-corner-capacity-20260929/` receipt. These are checks of the
argument, not an appeal to finite evidence as a proof.

Below m*, a path may have fewer than its maximum number of selected
nodes. A forward exchange can then create a new available exchange
to its RIGHT. The decreasing-priority assertion used above fails.
Thus we have NOT proved the normalization or whole-component recurrence
in those layers. In particular the 125-state eight-edge NN component
in area 012333 and the 3381-state eight-edge NN component in area
0123434 remain outside this result. General NN/DN collection in these
lower cyclic layers is still unproved.

## Lower layers require temporary redundant corners

2026-09-29 continuation. The maximum-layer proof cannot be extended by
simply choosing a different path that keeps every corner covering.
There is already an obstruction in area 012333. Let

    M={03,14,25},
    A=M+{01,02,12,34,45},
    B=M+{01,12,34,35,45}.

Both states cover all M and have eight selected edges. Their auxiliary
path occupancies are (2,1,2) on (01,13,34), (02,23,35), (12,24,45).
But A has NO actual flip neighbor covering all M. Its only possible
flips are 01->13 retaining 03, 12->24 retaining 14, 34->13 retaining
14, and 45->24 retaining 25. They make, respectively, 14,25,03,14
redundant. The remaining selected nonmaximal long 02 is redundant via
01,12 and supports no actual flip. This checks every natural triangle,
so allowing normal retained edges does not avoid the obstruction.

Nevertheless A and B belong to the same whole component. Retaining M,
the following six actual flips connect them:

    01->13 [03], 45->24 [25], 02->23 [03],
    23->35 [25], 13->01 [03], 24->45 [25].

Square brackets specify the retained corner. All five intermediate
states have 14 redundant; the retained 03 or 25 and the exchanged
short cover at every step. Thus temporary redundancy is required,
not an artifact of a poor choice of forward-move priority. This does
not itself give the recurrence for the whole 125-state component.

### Normalize entire corner chains, allowing temporary redundancy

We can use temporary redundancy systematically. The following extends
[ordered strict-chain normalization](COMPONENT_CHAIN_NORMALIZATION.md#ordered-normalization-of-every-strict-chain)
to ALL simultaneous-cover states, even those whose normal edges and
reversed corners initially contain a directed cycle. It is a structural
path theorem, independent of the word-functional proof.

Let S contain all original strict edges and consist of selected maximal
corners, all covering in A. These corners partition the vertices into increasing chains, with singleton chains
included. Let r(v) be the largest vertex in v's chain. Then A is joined
by actual flips retaining corners in S to the explicit state P(A):

* keep each selected normal edge vy with r(v)<r(y);
* replace each selected normal edge vy with r(v)>r(y) by yh, where
  h is the strict successor of v in its chain;
* retain S.

Here normals are relative to S. Other strict decorations can be included
in S; the theorem will be used with S=M. The endpoint has all normals
increasing in chain maximum, hence its normals together with reversed
S are acyclic. Every corner in S covers at the endpoint. Each inversion
edge is exchanged exactly once, and the total selected-edge count and
whole component are preserved. We do NOT assert that every intermediate
state has all S covering, or that P is constant on a component.

To prove this, process entire chains in decreasing order of their maxima.
Keep the previously processed union U absorbing for selected edges. In
the remaining vertices, the next chain B has largest terminal vertex,
so its terminal has no outgoing edge outside B. A normal edge vy leaving
an earlier vertex v of B has v<y<h, where h is v's strict successor:
a longer normal interval would contain the maximal corner vh.

Choose such an exit with smallest head y, ignoring edges entering U.
The short vy covers. An alternate v-to-y path cannot enter U and return,
cannot start with the strict vh because h>y, and would otherwise start
with a selected exit having smaller head. The long vh covers by the
block invariant. Hence vy->yh retaining vh is an actual flip.

This removes one exit from B and adds an edge entering B. Every other
corner of B keeps its cover, since its interval is disjoint from the
interior of vh. The retained vh keeps its cover by the flip criterion.
Thus we can repeat until B has no exit to the remaining vertices.
Corners of other unprocessed chains are allowed to become redundant
DURING this procedure.

At completion, U union B is absorbing. Any newly created bypass of a
corner whose endpoints remain outside this union would have to use one
of the added edges, hence enter B and never return. This is impossible.
Such corners therefore recover their covers. Previously processed corner
covers also persist, because paths starting in U cannot leave U and its
internal edges have not changed. These observations supply the invariants
for the next chain, and prove termination of the ordered construction.

Every inserted edge has increasing chain maxima and enters the processed
union, so it is never removed later. Every removed edge is precisely an
original inversion. Its replacement was originally absent: selecting both
would bypass its corner. Different inversions have different replacements,
since a strict head has a unique predecessor. This proves the displayed
endpoint formula and its exact path length.

Consequently, within any whole component selecting S, existence of a
simultaneous-cover state is EQUIVALENT to existence of a state whose
normals together with reversed S are acyclic. The reverse implication
is the usual bypass-cycle observation; the forward implication now uses
an actual path. These conditions are not equivalent state by state.
This does not identify all anchors P(A) in one component or collect their
NN/DN images. In the six-vertex obstruction, BOTH A and B are already
anchors, so this normalization alone cannot connect them.

Related Rust: graph-only `--joint-chain-normalization` checks the explicit
endpoint map, every prescribed flip, every completed block invariant and
final mixed acyclicity on all 7911 simultaneous-cover states of the 14
fixtures. The separate `--corner-occupancy` check finds the obstruction
above, checks its six-flip path and confirms that no all-cover path can
start at A. Its exploratory same-occupancy connectivity checks, allowing
temporary redundancy, pass in all 14 fixtures; this is NOT a general
same-occupancy connectivity theorem. Frozen sources and receipts are in
`lower-corner-normalization-20260929/`. General lower-layer whole-component
collection remains unproved.

## Complete component recurrences for cubes of paths on 3h vertices

2026-09-30 continuation. We now settle every edge layer in an unbounded
family, rather than only its maximum simultaneous-cover layer. The proof
uses explicit local flips, the ordered corner-chain preparation, and
independent smaller-component corrections. It does not use a basis
calculation or the separate component-expansion theorem.

### Anchors are subsets of one fixed diagram

First let G be arbitrary and M its full set of maximal natural corners.
The final alternating state A* from (JC1) is exactly M together with
EVERY normal edge whose endpoints have increasing corner-chain maxima.
Indeed, along a short-edge path ab->bc the endpoints a,c belong to the
same corner chain, so the comparison of the two chain maxima reverses.
At the last node ab, a has no strict successor: such a successor would
supply the next link. Thus r(a)=a<b<=r(b), and the last node is good.
Good nodes therefore alternate backwards from the last node of each path.

It follows that the anchors in an edge layer k are exactly the k-edge
subsets of A* containing M. Every state with all M covering reaches one
of these anchors by the preceding chain-normalization theorem. In
particular, at k=m*-1 the only anchors are A* with one normal edge
deleted. This is a reduction of the connectivity question, not a claim
that all such subsets belong to one component in an arbitrary diagram.

### The cube family and its three chains

Let n=3h with h>=2, and let G_n have the natural edges ij with
1<=j-i<=3. Its maximal corners are

    M={i(i+3) : 0<=i<n-3}.

Their three chains are the three residue classes modulo 3. Their maxima
are n-3,n-2,n-1, in that order. Divide the vertices into h consecutive
blocks of three. The increasing-chain-max normal edges are precisely
the three edges WITHIN each block. Thus an anchor consists of M and
an arbitrary subset of these h disjoint triangles.

Name the three edge types 01,02,12 according to their residues. We call
these types colors only for the following bookkeeping; they are not
colorings of the diagram. An anchor is a three-row binary array with
h columns, one column per triangle. Each row has at most h selected
edges. The weak components of the full selected graph are determined
by which of the three edge types occur: no types leave three chains;
one type joins its two chains; any two types join all three chains.

**Anchor connectivity theorem.** For this family, any two anchors
with the same selected-edge count and the same partition of the
vertices into weak components lie in the same actual flip component.
We prove this with moves on two adjacent blocks only.

### The six-vertex local moves

On two adjacent blocks use local labels 0,...,5 and keep the corners
03,14,25 selected. Write

    a=01, b=02, c=12, A=34, B=35, C=45.

These are the six possible anchor normals. A path below returns to
an anchor and leaves every unspecified anchor edge unchanged.

First, we may move a selected edge between the two positions of ANY
one type, provided the other position is empty. For a<->A the path
is 01->13->34, retaining 03 then 14. For c<->C it is
12->24->45, retaining 14 then 25. These are the proved slides between
consecutive corner chains and allow arbitrary anchor exterior.

For b->B, if either the a/A row or the c/C row is empty, the direct
path 02->23->35 is actual: neither 02 nor 35 has its two-edge normal
bypass. Otherwise use the preceding row moves to arrange a and C
selected. Now use

    01->13 [03], 45->24 [25], 02->23 [03],
    23->35 [25], 13->01 [03], 24->45 [25].             (CP1)

The edges A,c can independently be present or absent. With both present,
the six normal sets are exactly the six-vertex path recorded above;
all its retained edges and exchanged shorts cover. Deleting either
of the two unused edges preserves these cover tests. Finally undo
the preparatory row moves, restoring the whole exterior. Reversing
this path handles B->b. Thus each row can be rearranged independently.

Second, any two-edge selection in ONE triangle can be changed to either
other two-edge selection, with arbitrary selection in the other triangle.
The normal-long flip {a,b}<->{b,c} is immediate. For the other exchange,
with b absent initially, we have

    {a,c} -> {13,c} -> {13,23} -> {a,23} -> {a,b},   (CP2)

retaining, respectively, 03,13,03,03. The temporary edges 13,23 are
absent in an anchor. Each cover test is inside [0,3]; the selected
corners 14,25 and all other-triangle edges cannot affect it. This
proves {a,c}<->{a,b}, and composition gives the third comparison.
Reverse the six-vertex order to obtain the same moves in the upper
triangle. These paths may temporarily make another corner redundant.

We can now classify ALL two-block anchors, without assuming an
unproved table. Their row counts are (p_0,p_1,p_2), each between zero
and two. With at most one nonzero row, the partition fixes the row,
and row moves connect every arrangement with that count. With at least
two nonzero rows, all three chains are connected. Row moves and the
triangle exchanges connect every count vector with the same total:

* If the third row is nonempty, arrange a donor and a third-row edge
  in one triangle, with the receiving type absent there. Apply (CP2)
  or its two-edge companions, retaining the third-row edge.
* If only donor and receiving rows are nonempty, a transfer preserving
  connectivity has counts (2,1,0) on these rows. Arrange the receiving
  edge beside one donor. Exchange that donor for the third type; move
  the new third-type edge to the other triangle; there exchange it for
  the receiving type, retaining the remaining donor. The result has
  counts (1,2,0).

Each operation changes one donor into one receiving type, respects the
capacity two, and retains at least two nonzero rows. These transfers
connect the count vectors: move an entry above its desired value to
one below it. If doing so would leave only one nonzero row, first use
a deficient third row instead. The desired vector itself has at least
two nonzero rows, so such a choice exists. The sum of coordinate
errors decreases at every transfer. Row moves then give the specified
positions. This proves the local classification.

### Move through arbitrarily many blocks

Every local path lifts to two adjacent blocks in G_n. Its edges have
both endpoints in that six-vertex interval. An increasing alternate
path testing their covers cannot leave the interval and return.
All other selected edges, including strict corners entering or leaving
the interval, therefore leave the local cover tests unchanged. The
path restores the six-vertex anchor configuration before the next move.

Adjacent-block row moves rearrange each of the three rows arbitrarily.
Now suppose at least two rows are nonempty and we want to transfer one
edge from row U to row V without exceeding capacity h or losing
connectivity. If the third row W is nonempty, independently rearrange
rows so that the first column contains U,W but not V. The two-block
classification changes U to V there, fixing the remaining local edges.

If W is empty, U has at least two edges, V at least one and V has an
empty position. Arrange U in each of the first two columns and V only
in the second of them. In that second column change U to W, retaining
V. Move W to the first column, and there change W to V, retaining U.
Every use of the two-block classification has all three chains locally
connected at both endpoints. The final row counts are the desired
single transfer U->V, with W empty again.

The same decreasing coordinate-error argument connects any two feasible
count vectors with at least two nonzero rows. Finish by rearranging rows
to their desired positions. For the one-row and empty cases row moves
already suffice. This proves the anchor connectivity theorem for every
h>=2. The proof gives a terminating construction; it is not induction
from a finite list of globally enumerated components.

### Isolate the connected component in every layer

Let k=n-3+m. For every 2<=m<=3h there is exactly ONE connected whole
component C_k selecting all M and containing a simultaneous-cover state.
Existence follows by choosing an anchor with m normals and at least two
nonempty rows. For uniqueness, normalize any such state to its anchor;
normalization preserves its edge count, weak partition and actual
component. The anchor theorem connects all the resulting anchors.

For an eligible NN or DN source L with natural graph G_n, form B(D)
for every other whole source component D in layer k as follows:

1. If a maximal corner is absent, delete it. This is one whole smaller
   component, exactly as before.
2. Otherwise, if D is disconnected, concatenate its induced weak-block
   diagrams, preserving order inside each block. The proved block
   reordering lemma gives one whole smaller component, with the same
   K and E. Natural area decreases because G_n is connected and some
   natural edge joins different selected weak blocks.
3. Otherwise D is connected and selects all M. By uniqueness it has
   no simultaneous-cover state. Mark M strict and apply the alternating
   corner-deletion formula (JC3). Every image is a union of whole
   components of smaller diagrams, independently of any expansion.

Let epsilon=1 for NN and epsilon=0 for DN. The full-layer identities
now give the complete signed component recurrence, for BOTH X=K,E,

    X(C_k) = X(F_k(R)) + epsilon X(F_(k-1)(R))
               - sum_(D in F_k(L), D != C_k) B_X(D).  (CP3)

Every final diagram decreases the original induction order. Every other
component in this layer already has the independent smaller expression
just specified. Above k=2n-3, simultaneous corner covers are impossible,
so connected components reduce by (JC3) as well. Below k=n-1 no selected
graph is connected. Missing corners and disconnected components always
use items 1 and 2. Thus this gives component recurrences for EVERY layer
of the cube family, including all its lower cyclic layers.

No saturation assumption on the eligible source is needed. To choose a
native recurrence for a full-envelope component, marking/unmarking its
selected maximal corners preserves that whole component. For n=6 use
NN at w=2,x=3,z=5, with 03 unmarked. For n>=9 use DN at
u=n-7,w=n-4,x=n-3,z=n-1 and unmark the upper corner (n-6)(n-3),
keeping the other maximal corners strict. These are the established
ND/DD inheritance steps. The NN target lowers natural area by one;
the DN target keeps area and lowers area moment by two.

### The former 125-state case and verification

For area 012333 and strict 14,25, the formerly open eight-edge component
has m=5. Its anchors are the six deletions of one normal edge from
M plus the two full triangles. The theorem now connects them and gives
its full recurrence. The two actual NN target layers contain 23 whole
components with 210 states. The other source components comprise 13
missing-03 components with 84 states and one all-corners-selected
singleton. Alternating deletion of that singleton gives seven whole
smaller terms. Thus the checked recurrence accounts for 125=210-84-1.
The singleton's corners are everywhere redundant, so a single inactive
corner deletion can replace its alternating expression if desired.

Related Rust: graph-only `--cube-anchor-paths` checks 80 instances of
(CP1), (CP2), the consecutive slides and reflected triangle moves, with 236
actual flips. The local path table has 822 ordered
anchor pairs in 12 classes. The global row/count construction is checked
on ALL anchors for h=2,3,4 and bounded samples for h=5,6, always replaying
its local paths in the full global graph. Local BFS supplies a fixed
six-vertex path table; no global component search supplies these paths.
`--cube-layer-recurrences` checks every correction image and every final
diagram in all five connected-support NN layers for n=6 and all eight
DN layers for n=9. Sources and logs are frozen in the external
`cube-component-recurrences-20260930/` receipt.

This completes the NN/DN component step for G_(3h), not for arbitrary
ordinary diagrams. Its special input is the three-row triangle-block
anchor geometry. An arbitrary graph can have different corner-chain
lengths and more interacting chains. Neither the two-block classification
nor the row-transfer argument has been proved in that generality. The
3381-state eight-edge component in area 0123434 remains outside this
family, and the general Motzkin/Dyck recurrence goal remains open.

## Triangle exchange with a covering outer edge

2026-09-30 continuation. We extend the four-flip move (CP2) to arbitrary
ordinary exterior. The retained outer edge need not be strict or maximal,
and the states need not be anchors. We give an exact endpoint criterion.

Let a<b<c<h and suppose A selects ah,ab,bc and omits ac. Put

    B=A-bc+ac.

**Theorem.** The following four-flip path from A to B is actual if and
only if ah and ab cover in A and ac covers in B:

    ab->bh [ah], bc->ch [bh],
    bh->ab [ah], ch->ac [ah].                          (OC1)

All new edges are natural, being inside ah. Every exchanged edge is
normal, since it lies properly inside the natural edge ah. Thus all
strict decorations of the original diagram are retained. This is a
component-membership theorem; it does NOT assert X(A)=X(B) pointwise.

Necessity follows from the first and last flips. For sufficiency, first
observe that bc covers in A. Otherwise its bypass survives in B and,
preceded by ab, bypasses the assumed cover ac. Also bh and ch are absent
in A, since either would bypass ah using ab or ab,bc. The first flip
is therefore actual and produces a covering bh. The cover test for bc
is unchanged: removing ab and inserting bh cannot affect a path from
b to c. Hence the second flip is actual too.

After these two steps, ah still covers. Any new bypass would have to
use bh or ch. In the first case its prefix is an a-to-b bypass of ab
in A; in the second its prefix is an a-to-c path in A-bc, hence a
bypass of ac in B. Both are impossible. The retained bh covers by the
second flip, so bh->ab retaining ah is actual. This third move cannot
destroy the cover of ch: its changed edges start below c and cannot
occur on an increasing c-to-h path. The final flip is therefore actual,
and its endpoint is exactly B. This proves the criterion with no
assumption on other selected edges or their cover status.

Order reversal gives the dual. For d<a<b<c, if A selects dc,ab,bc and
omits ac, put B=A-ab+ac. The path

    bc->db [dc], ab->da [db],
    db->bc [dc], da->ac [dc]                           (OC2)

is actual exactly when dc and bc cover in A and ac covers in B.
Again the retained outer edge dc may be normal. Order reversal here
establishes an actual path, not a valuation-preserving relabeling claim.

For anchors, a selected strict successor ah or predecessor dc supplies
the outer cover automatically. Thus only the retained short at the
initial endpoint and the new ac at the final endpoint need checking.
Intervening normal paths may violate these hypotheses: the unguarded
cube-family exchange must not be applied to arbitrary anchor exterior.

Related Rust: graph-only `--outer-cover-pivots` checks the exact
three-cover criterion in both directions on all eligible configurations
in 14 fixed NN/DN diagrams, including states that are not simultaneous
corner covers. It checks 157728 configurations and 33498 valid four-flip
paths; 4128 of these use a nonmaximal, hence normal, outer edge. The
proof above is uniform; these finite checks are supplementary. Frozen
sources and logs are in `unequal-chain-anchor-recurrences-20260930/`.

## A checked whole-component recurrence with unequal chains

2026-09-30 continuation. We now resolve the previously open seven-vertex
area 0123434 example, in every edge layer. This is a FINITE constructive
certificate for that diagram, separate from the preceding uniform lemma
and from the uniform cube-family theorem.

The maximal corners are M={04,26}. Their chains are {0,4}, {2,6},
and the singletons {1}, {3}, {5}. The full alternating anchor is

    A*=M+{02,12,13,14,34,35,36,45,46,56}.               (UC1)

Every simultaneous-cover state reaches a subset of (UC1) containing M,
by the proved ordered chain normalization P. We use anchors only to
locate whole components; we do not replace the sum over a component
by its much smaller anchor sum.

### Actual paths between anchors

We use four kinds of verified connections, retaining arbitrary exterior:

* A single actual flip whose endpoints are both anchors.
* A two-corner slide whose two actual flips both pass their cover tests.
* The four-flip paths (OC1), (OC2), with their stated cover hypotheses.
* If U,V are actual flip neighbors and all M cover at BOTH endpoints,
  concatenate the reversed normalization of U, the flip U->V, and the
  normalization of V. This gives the actual path P(U)->U->V->P(V).

The last construction uses the general preparation theorem and may
pass through temporary redundant corners. It is not a claim that
normalization carries a single flip to a single flip. Every stored
connection includes its full actual-flip trace.

The following spanning trees connect ALL connected anchors in each
possible layer. States and paths are given explicitly in the external
`anchor-certificate.txt`, with its edge-mask convention fixed by the
lexicographically ordered natural edges of area 0123434.

| Selected edges k | Connected anchors | Tree edges | Replayed actual flips |
| --- | ---: | ---: | ---: |
| 6 | 105 | 104 | 279 |
| 7 | 200 | 199 | 632 |
| 8 | 195 | 194 | 687 |
| 9 | 118 | 117 | 451 |
| 10 | 45 | 44 | 213 |
| 11 | 10 | 9 | 44 |
| 12 | 1 | 0 | 0 |

The independent replay constructs all 2^10 subsets of the normal part
of (UC1), tests their weak connectivity, and derives the expected anchor
set in every layer. It then checks every stored flip and every endpoint,
and verifies that each tree reaches EXACTLY the expected set. It uses
no enumeration or search of whole source flip components. Thus the
certificate checks 674 anchor states, 667 tree edges and 2306 actual
flips, rather than assuming a component profile obtained elsewhere.

It follows that each k=6,...,12 has exactly one connected component C_k
selecting M with a simultaneous-cover state. Every such state reaches
one of the checked anchors in its own whole component, and the tree
connects all of them. Existence is supplied by any root anchor. The
known maximum simultaneous-cover bound excludes higher k, and a
connected graph on seven vertices requires k>=6.

### The complete NN recurrence

Use the eligible NN contact w=2,x=3,z=6, with 04,26 strict. The target
R deletes 26 and marks 36 strict; its area is 0123433. In each layer,
every other source component D independently reduces as follows:

* A disconnected D becomes one whole component of the smaller diagram
  obtained by concatenating its induced weak blocks.
* A connected D other than C_k has no simultaneous-cover witness.
  Alternating deletion of M, as in (JC3), expresses it in whole
  components of smaller diagrams.

Both corners are strict in this source, so there is no missing-corner
sector. With B(D) denoting the indicated smaller expression, we obtain
for BOTH X=K,E, with identical integer coefficients,

    X(C_k) = X(F_k(R)) + X(F_(k-1)(R))
                - sum_(D != C_k) B_X(D).              (UC2)

Every correction has independently proved whole-component status and
smaller natural area. The target also has smaller natural area. The
same corrections reduce the other source components directly. Above
the common-cover maximum all connected components use alternating
deletion; below the connected minimum all components are disconnected.
This completes the NN component recurrence for this fixed decorated graph.

In particular, C_8 is the formerly open 3381-state component. Its root
anchor is {02,04,12,13,14,26,34,35}. The actual target layers contain
162 whole components with 5005 states. The other source components
comprise 74 disconnected components with 1039 states and 16 connected
no-common-cover components with 585 states. Their alternating images
give 180 whole deletion terms. Thus the complete recurrence accounts
for 3381=5005-1039-585, with 244 positive and 172 negative whole terms
before cancellation. These counts check the explicit recurrence;
the existence of (UC2) rests on the paths and independent reductions,
not on equality of state counts alone.

### Verification and precise remaining gap

Related Rust: `--anchor-generator-graph` constructs the local witnesses,
normalization traces and seven spanning trees, then verifies every
whole correction component. The separate `--verify-anchor-certificate`
mode replays the saved trees without a source-component search. Across
the seven recurrences it checks 21577 survivor states, 415 reordered
block corrections with 4236 states, and 553 alternating source corrections
with 4438 states, yielding 2167 whole deletion terms. Both directions
of every reordered-block flip graph are checked. The receipt includes
source, exact commands, the full certificate, logs and hashes.

The same generator audit also records its limitations. Its anchor graph
still splits the 84-state complete-graph component, a 16-state empty-corner
NN component and a 121-state DN component in the fixed fixtures. These
are limitations of THIS generator set, not failures of their component
recurrences. The 84-state component already has its independent completed
signed recurrence. In particular, a failed generator connection must not
be promoted to a newly open component-expansion case.

We have not proved that these moves generate all component connections
in arbitrary diagrams. The projected-flip construction requires both
raw endpoints to have all corners covering, and the outer-cover lemma
has genuine cover hypotheses. General paths may cross other redundant
states not accounted for by these constructions. Completing that argument,
or directly repairing the RHS coefficients, remains necessary for the
general Motzkin/Dyck NN and DN recurrence theorem.

## The interval graph of corner chains

2026-09-30 continuation. We give a global description of the anchor
geometry for an ARBITRARY ordinary diagram, then lift one class of its
edge rearrangements to actual flips. This is not yet the general component
recurrence. In particular, contracting a chain below is a device for
organizing paths, not a coloring or HRV identity.

Let M be all maximal natural corners, marked strict after the envelope
reduction. Its directed components are chains. Write r(v) for the last
vertex of the chain containing v, and let t be the number of chains.
The proved preparation theorem sends any simultaneous-cover state, by
actual flips, to an anchor: M together with selected normal edges uv for
which r(u)<r(v). All anchors are subsets of the fixed A* in (UC1)'s general
construction, with M retained.

Contract each corner chain to one vertex, labeled by its last vertex.
Keep a separate edge copy for every normal edge of A*. Call the resulting
multigraph H. An anchor A gives the spanning edge subset H(A), including
vertices of degree zero. Direct its edges by increasing chain labels.

### One short-edge path for each pair of chains

No normal natural edge has both endpoints in one corner chain. Indeed,
an interval between nonconsecutive vertices of the same chain properly
contains a maximal corner, and a consecutive pair is itself a corner.

A short-edge link uv->vh, retaining uh in M, exchanges the two chain
labels. Thus an entire auxiliary short-edge path stays within ONE unordered
pair of chains. In fact each pair has AT MOST ONE such path.

To see uniqueness, a normal edge uv has a predecessor on its short-edge
path exactly when v has a corner predecessor p. In that case p<u: the
alternative u<=p would make uv equal to or properly contain the corner
pv. The predecessor is the natural normal edge pu. Consequently the
first node of any short-edge path must end at the first vertex of one
of its two corner chains. Its tail lies in the chain which starts earlier.
There can be at most one such tail before the later chain's first vertex:
if u<u'<v were two, the natural interval uv would properly contain the
corner from u to its chain successor, which is at most u'.

It follows that H has one parallel class for each nonempty short-edge
path. If that path has l nodes, the class has exactly ceil(l/2) copies:
we retain its last node and alternate backwards. Its retained nodes are
ordered along the path, and both their ordinary endpoints strictly
increase. This last order will supply the actual two-flip slides below.

### An explicit interval representation

For an original vertex v, let R(v) be its greatest natural neighbor to
the right, or v when it has none. The ordinary natural graph is the
intersection graph of

    I_v=[v,R(v)].                                      (CQ1)

Indeed, for u<v, the intervals intersect exactly when v<=R(u), which
is exactly the natural-edge condition. The right endpoints R(v) are
nondecreasing, by closure under subintervals.

For a corner chain B, the intervals I_v, v in B, form a connected union:
consecutive chain vertices u,h share the corner uh, so I_u and I_h
intersect. Their union is exactly

    J_B=[min(B),R(max(B))].                            (CQ2)

Two such unions intersect if and only if some natural edge joins the
chains. Every such edge lies on their unique short-edge path, whose last
node belongs to A*. Conversely every edge of A* is natural. Therefore
(CQ2) is an interval representation of the SIMPLE graph underlying H.
In particular, keeping only the alternating copies does not remove any
adjacency between distinct chains.

Every clique of this simple graph has a natural-clique witness in the
original diagram. Pairwise intersecting closed intervals J_B have a
common point: the largest left endpoint is at most the smallest right
endpoint. For each B choose v in B with that point in I_v. These vertices
form a natural clique by (CQ1). Thus each maximal clique of H is the
projection of some maximal natural clique. This supplies the geometric
triangles needed for a possible lifting argument; it does not establish
the cover tests of any selected-state flip.

There is also a useful restriction on separators. A maximal natural
clique [a,b], with corner ab, contains two vertices of the same corner
chain only for the pair a,b. Otherwise a different maximal corner would
lie properly inside [a,b]. Its projection therefore has b-a distinct
vertices. The intersection of TWO different maximal natural cliques has
no chain identifications at all, for the same reason.

Consequently, if a connected natural graph on at least three vertices
has no articulation, its projected simple graph has at least two vertices
and no articulation either. For completeness, order the maximal natural
cliques by their left endpoints. Both endpoint sequences strictly increase.
Connectedness makes consecutive cliques intersect, and a one-vertex
intersection would separate everything to its left from everything to
its right. Thus consecutive intersections have at least two vertices.
Every clique has at least three vertices, and its projection has at least
two. Consecutive projected cliques still share at least two DISTINCT
vertices. After deleting any one projected vertex, their remaining
nonempty cliques still meet consecutively. Their union is connected.

### Connected anchors exist in every feasible layer

Contraction of the fixed forest M preserves weak components. Hence A
is connected exactly when H(A) is connected. With k=|A|, the multigraph
H(A) has k-|M| edges and t=n-|M| vertices. Its cycle rank is exactly that
of A, also when A is disconnected.

If the original natural graph is connected, H is connected by (CQ2).
Choose one edge copy for each edge of a spanning tree of its simple graph,
then insert further unused copies in any order. Lifting these selections
back to A* gives connected simultaneous-cover anchors of EVERY size

    n-1 <= k <= m*.                                   (CQ3)

Every lifted state is a subset of A* containing M, so all corners cover.
There are none below n-1 by connectedness, or above m* by the proved
corner-capacity bound. This proves existence throughout the interval,
not uniqueness of the whole component containing such a state.

## Rearranging parallel copies of a quotient cover

Continue with an arbitrary anchor A. Suppose a selected pair of chains
B,D, with r(B)<r(D), is a COVER in the directed simple support of H(A):
there is no directed route from B to D through another chain. This holds
in particular when their labels are consecutive among all chain labels.
We prove that the selected copies in this parallel class can be moved to
any other positions with the same cardinality, by actual flips in the
original diagram, retaining every other anchor edge at the endpoints.

First EVERY selected normal edge uv from B to D covers in A. Any bypass
would give a directed walk of nondecreasing chain labels. The assumed
quotient cover excludes an intermediate chain. The walk must therefore
use a single other normal edge u'v' from B to D, with corner-chain paths
before and after it. It would require u<=u' and v'<=v. But the different
copies of this parallel class have both endpoints increasing together,
as just proved. These inequalities are impossible for another copy.
The same argument applies to any proposed anchor with the same quotient
support, including after rearranging copies.

Consider consecutive positions of this parallel class. On its auxiliary
short-edge path they have the form

    ab -> bc -> cd,      a<b<c<d,
    ac,bd in M.                                       (PC1)

Suppose ab is selected and cd is absent. The desired replacement is

    A' = A-ab+cd.

Both A and A' are anchors and have the same directed quotient support.
The two flips are

    ab -> bc [ac],       bc -> cd [bd].                (PC2)

For the first flip, ac covers because A is an anchor, and ab covers by
the preceding quotient-cover argument. The inserted bc is normal and
absent; it has the opposite chain-label order from every anchor edge.
The first flip is actual and makes bc a cover.

The retained bd covers after this first flip. Otherwise its new bypass
must use the inserted bc, since bd covered initially. Its remaining
c-to-d path uses only edges of A-ab, and survives in A'. It would bypass
cd in A', contradicting the same quotient-cover argument there. Thus
both required covers hold for the second flip, which is actual and has
endpoint A'. The inverse path gives the reverse exchange. Every exchanged
edge is normal, being properly inside ac or bd; all original strict
edges remain selected. Other selected edges of the diagram are arbitrary.

Any two subsets of an ordered list of copies with the same size are
connected by neighboring occupied/vacant exchanges. Applying (PC2)
therefore proves the stated full rearrangement, not merely one local move.
For example, repeatedly move a selected copy into the next vacant position
until the last m positions are selected. The number of inversions of this
binary list strictly decreases. The quotient support stays fixed, so the
cover hypothesis remains true at every step. We may normalize all quotient
cover classes in a fixed order by this finite procedure. It gives an actual
path within the SAME original whole component and changes no occupancy
count or quotient support.

### Verification and the remaining component obligation

Related Rust: graph-only `--anchor-quotient-scan` checks all 2055 ordinary
area sequences on one through eight vertices. It independently contracts
M with the maintained `Graph::contract_edge` API, checks (CQ1)--(CQ2),
the one-path-per-pair and multiplicity statements, clique projections,
and all 3232 quotient-triangle witnesses. It constructs 2790 connected
anchors spanning every feasible layer in the 626 connected diagrams,
checking all original corner covers. The no-articulation conclusion is
checked on all 196 applicable diagrams. No source-component search occurs.

The separate `--anchor-parallel-slides` mode checks all anchors in the
14 existing NN/DN fixtures. It checks every quotient cover against original
covers, replays neighboring-copy exchanges in both directions, and performs
the terminating normalization with fixed quotient support: 1806 anchors,
5311 selected quotient covers, 6316 original cover tests, 1704
neighboring swaps and 2320 normalization flips. It too uses no
source-component enumeration. Exact counts, frozen consumer, commands
and logs are in `corner-chain-quotient-20260930/` under the external request
folder. These finite checks supplement the uniform proofs above.

The general NN/DN recurrence is STILL UNPROVED. We have not shown that
arbitrary connected selections of this interval multigraph lift to paths
between their anchors. In particular, a pair joined by a selected route
through other chains is outside (PC2)'s proved rearrangement theorem.
Ordinary graph exchanges at such a pair can fail the original cover tests.
The earlier cube-family detour is one proved way past that obstruction,
but there is no general detour or whole-component collection theorem yet.
The six-vertex cube obstruction makes this restriction concrete. With
M={03,14,25} and normals {01,02,12,34,45}, the chain labels are 3,4,5.
The pair 3,5 has selected route 3->4->5. Its copy 02 is redundant through
01,12, so the direct slide 02->23 [03] cannot start. The earlier six-flip
path nevertheless replaces 02 by 35 in the same whole component; all
five intermediate states have corner 14 redundant. This is a needed
extension of (PC2), not a new unsolved finite recurrence.

The next section lifts one class of transfers between different chain
pairs. General transfers remain open. Neither the interval representation,
the clique witnesses,
nor the existence of an anchor in every layer supplies that lift.

Thus the quotient gives a precise global setting for the missing paths,
and (PC2) removes the cover pairs from their parallel-copy problem. A
successful use in the recurrence must still identify the whole surviving
component, or repair the actual RHS coefficients directly, before applying
the existing smaller-component corrections. We do not sum K or E over
quotient subsets in place of the original whole components.

## Lifting a quotient fork and obtaining one sink in each block

2026-09-30 continuation. We now lift one class of transfers BETWEEN
chain pairs, and iterate it to a global normal form. This extends the
preceding parallel-copy theorem. The endpoint need not be unique, and
we do not assert that its component has been isolated by a recurrence.

### Put the two selected copies at a common tail

The LAST copy in any nonempty parallel class B,D, with r(B)<r(D), has
the form

    r(B) -> v,       v in D.                           (QF1)

Indeed the last node uv of its short-edge path has no successor. Thus
u has no corner successor and equals its chain's last vertex. Since
u<v<=r(v), this is the chain with smaller label. Also v is the first
vertex of D above u: an intervening predecessor would give a maximal
corner properly inside uv.

Suppose the selected quotient support has TWO outgoing covers

    r->s, r->t,       r<s<t.                           (QF2)

There is no selected directed route from s to t, since it would make
r->t redundant. By (PC2), move selected copies in both classes to their
last positions, preserving all occupancy counts and quotient support.
In particular we select

    rb, rc,          r(b)=s, r(c)=t,

with common ordinary tail r and r<b,c. Both edges cover in the original
anchor. Since rb and rc are natural, so is the edge between b,c.
There is no selected edge between the chains s,t: that would already
be a selected s-to-t route.

If b<c, the single actual flip

    rb -> bc [rc]                                     (QF3)

retains a covering long and exchanges a covering short. Its endpoint
is an anchor: the inserted edge has chain labels s<t. It transfers
one copy from r,s to s,t, retaining the chosen r,t copy.

If c<b, first perform the actual flip

    rc -> cb [rb].

The inserted cb has chain labels t>s. Let h be the corner successor
of c. It exists and lies above b: c<t and b<=s<t, while a successor
at or below b would make the natural edge cb contain a maximal corner.
The desired second flip is

    cb -> bh [ch].                                    (QF4)

We check its retained corner without imposing any exterior restriction.
Immediately after the first flip, every corner still covers. Otherwise
its new bypass would use cb. Contracting chains in that bypass gives
a directed closed walk using the new step t->s and otherwise only
increasing chain labels. Removing that step leaves a selected s-to-t
route from the old quotient support, which (QF2) excludes. A bypass
without cb would already have existed in the original anchor.
Thus ch covers. The short cb covers because it was just created by an
actual flip. The second flip is actual and inserts the normal edge bh,
with chain labels s<t. Its endpoint is an anchor, transferring one copy
from r,t to s,t while retaining the chosen r,s copy.

All displayed triangles are natural, all exchanged edges are normal,
and every original strict edge stays selected. These moves allow
arbitrary exterior and arbitrary additional selected copies. The
preparation by (PC2) may change the positions of other copies in the
two prepared classes; it changes neither their counts nor the quotient
support. No other class is changed before (QF3) or (QF4).

### A terminating normalization for every anchor

Assign to an anchor A the integer

    tau(A) = sum_(uv normal in A) r(u).                (QF5)

The preparation slides leave tau unchanged. Each fork move strictly
increases tau: it removes one normal with tail-chain label r and inserts
one with tail-chain label s>r. The number of selected normals is fixed,
and tau is bounded above by that number times n-1. Therefore repeatedly
choose two outgoing quotient covers and apply (QF3) or (QF4). This
procedure terminates, using only actual flips, at an anchor whose
quotient support has at most one outgoing cover at every vertex.

Such a finite directed support has a unique sink in each weak component.
To see this, follow its unique outgoing cover when one exists. Every
edge decomposes into a path of covers, so its two endpoints have the
same eventual sink. Weak connectedness then makes that sink common
to the entire block. It is the block's greatest chain label.

Finally apply (PC2) to each remaining quotient cover so its last copy
is selected. By (QF1), the terminal vertex of its tail chain reaches
the terminal vertex of its head chain: follow the selected last copy,
then the fixed corner chain. All original vertices first reach their
own chain terminal along M. Following the quotient covers now shows
that every original vertex reaches the greatest vertex of its weak
block. The original selected relation therefore has exactly one sink
in each weak block, and ALL maximal corners still cover.

**Conclusion.** Every whole ordinary component having a simultaneous
cover witness contains a state with simultaneous corner covers and one
sink in each weak block. The path is constructive: first use the proved
ordered corner-chain preparation, then the fork procedure and final
parallel-copy normalization. It preserves the selected-edge count,
the weak partition, and every strict edge throughout. In the connected
case, the final state's HRV partition is (n).

This is stronger than merely activating one reachability while letting
other corners lose their covers permanently. It does not claim that
all these one-sink states lie in one component or that they have a
unique normal form. It also does not replace any component sum by
this single representative.

### Verification and next missing step

Related Rust: graph-only `--anchor-fork-normalization` starts from every
anchor in the same 14 NN/DN fixtures. It replays every preparation and
fork flip, verifies all final corner covers and strict-edge retention,
and checks that tau increases at every fork. The maintained `Graph`
and `Poset` APIs independently check preservation of weak blocks and
reachability of the greatest vertex from every member of each block.
The explicit bound on fork steps is the number of normal slots times n.
There is no source-component search. Source, command and logs are frozen
with the other modes in `corner-chain-quotient-20260930/`. Across 1806
anchors, the check uses 967 forks (891 direct and 76 reversed), 3367
actual flips including preparation, and 2383 verified weak blocks.
The longest path has 11 flips; 1133 starting anchors change.

The remaining component argument can now start at this more constrained
representative. We still need paths comparing such representatives,
including rearrangement of noncover parallel classes and further
transfers between chain pairs, or a direct whole-component repair in
the recurrence target. The strict increase of tau proves termination
of this normalization only; it does not prove confluence or general
NN/DN collection.

## Sweep aside the obstructions and restore them after the slide

2026-09-30 continuation. We now remove the quotient-cover restriction
from the parallel-copy theorem. The missing move is exactly a controlled
excursion through redundant-corner states. We first prove it for arbitrary
selected ordinary exterior, without an anchor assumption.

Let a<b<c<d. Suppose A selects ac,bd,ab, omits cd, and ac,bd cover in A.
The two retained edges need not be maximal or strict. Put

    B=A-ab+cd.

**Crossing-cover transport.** There is an explicit actual-flip path from
A to B, keeping all other selected edges at its endpoints and every
original strict edge throughout. We do NOT require ab to cover initially
or cd to cover finally.

Let L consist of the v with a<v<b and av selected, and let R consist of
the v with c<v<d and vd selected. Perform the following operations:

1. For v in L in increasing order, flip av->vc retaining ac.
2. For v in R in decreasing order, flip vd->bv retaining bd.
3. Flip ab->bc retaining ac, then bc->cd retaining bd.
4. Undo step 1 in reverse order, then undo step 2 in reverse order.

Every displayed edge is natural, being inside one of ac,bd. Every exchanged
edge is normal for the same reason. The path has exactly

    2+2|L|+2|R| <= 2(n-3)                             (CS1)

flips. All its intermediate cover tests are justified as follows.

In step 1, av covers when it is moved: any alternate a-to-v path would
start with a selected edge to a smaller vertex, and all such outgoing
edges have already been removed. The retained ac starts as a cover and
stays one after each actual flip. These changes start below b and thus
affect no path inside [b,d]; in particular bd still covers.

In step 2, vd covers when it is moved: an alternate v-to-d path would
end with a selected edge from a larger vertex, and all those incoming
edges have already been removed. The retained bd stays a cover. These
changes have their other endpoint above c and affect no path inside
[a,c]. The edge ac therefore remains a cover too.

We have removed all selected edges from a into (a,b), so ab now covers.
Also bc is absent: its presence with ab would have bypassed ac initially,
and neither sweep inserts bc. The first core flip is actual. After it,
bd still covers. A new bypass of bd would have to start with the newly
inserted bc, but no c-to-d path remains: cd is absent, and all incoming
edges to d from (c,d) have been removed. Thus the second core flip is
actual and produces B with the temporary sweep changes still present.

It remains to justify RESTORATION; preparing only the forward slide is
not enough. For v in L, the net core change ab->cd affects no path inside
[v,c]: ab starts below v, and cd ends above c. Step 2 affects none of
those paths either. Therefore the required cover of vc is exactly the
one in the valid reversal of step 1 without the core change. The retained
ac covers after the core: the second core flip removes bc and inserts
an edge leaving c, so cannot destroy its cover. Undoing step 1 is actual
throughout. Its changes start below b and leave the cover of bd intact.

For v in R, the net core change likewise affects no path inside [b,v]:
ab starts below b and cd ends above v. Step 1 has now been restored.
Hence every required cover of bv is exactly the one in the valid reversal
of step 2. The retained bd covers after the core and was unaffected by
the first restoration. We can undo step 2 completely. The endpoint is
exactly B, proving the theorem with all exterior edges restored.

For the old six-vertex cube obstruction, take a=0,b=2,c=3,d=5.
Then L={1}, R={4}, and this construction is precisely

    01->13 [03], 45->24 [25], 02->23 [03],
    23->35 [25], 13->01 [03], 24->45 [25].             (CS2)

The same mechanism now works for arbitrary numbers of intervening edges
and arbitrary ordinary exterior. Other corners may be redundant during
the sweeps; they need not be covers to remain selected.

## Pack every parallel class, including noncovers

For an arbitrary anchor, consecutive good positions on any auxiliary
short-edge path have the form ab,cd with maximal corners ac,bd, as in
(PC1). Both retained corners cover automatically. Thus (CS1) moves a
selected copy from either position to the other whenever that other
position is vacant. Its inverse supplies the reverse move.

**Packing theorem.** Fix the number m_e of selected copies in each
parallel class e of the corner-chain multigraph H. ALL anchors with
these occupancy counts lie in one original whole component. They have
an explicit path to the single packed anchor P(m): select the last m_e
copies in every class, along with M.

The proof is the neighboring occupied/vacant exchange argument from
(PC2), now using (CS1) in EVERY class. Each exchange restores all other
edges, and ends at another anchor. The inversion count of the binary
copy list decreases, so packing terminates. The endpoint depends only
on the occupancy counts. This proves uniqueness of the representative
WITHIN one occupancy vector, not uniqueness for a whole edge layer.
Distinct vectors can belong to the same whole component.

In particular, the earlier restriction to selected quotient covers is
superseded for parallel-copy rearrangement. The other class of missing
moves is still real: changing the counts between different chain pairs.
The proved quotient forks supply some such changes but not all of them.

The packed representative also realizes quotient reachability exactly.
For every selected pair r->s its last copy is selected. By (QF1), this
edge starts at the terminal vertex r and enters the chain ending at s;
the fixed corners continue the path to s. Conversely any path in the
original anchor projects to a nondecreasing path of chain labels.
Therefore, writing h_H for the greatest reachable chain label in the
selected quotient support,

    h_(P(m))(v)=h_H(r(v)).                             (CS3)

Every original reachable vertex can itself continue to its chain terminal,
so there is no larger reachable vertex missing from this formula.
This identifies the HRV map of P(m); it does NOT identify the value of
an entire component with the value of its packed representative.
Combining packing with the preceding fork procedure gives a packed
one-sink representative in every component having a common-cover witness.
We have not proved uniqueness of these representatives across vectors.

Related Rust: `--crossing-cover-slides` replays (CS1) for all eligible
states and retained crossing covers in the 14 fixed NN/DN fixtures,
including normal retained longs and non-anchor states. It checks every
flip, exact restoration, both final retained covers, and preservation
of the original strict edges. `--anchor-packet-packing` packs every
anchor in the fixtures, including noncover classes, and independently
checks (CS3) with the maintained Poset API. Neither mode searches
complete source components. Frozen sources, commands, logs and hashes
are in `crossing-slides-three-chains-20260930/` under the request folder.

## Complete recurrences for three corner chains without articulation

2026-09-30 continuation. The unrestricted packing theorem gives complete
NN/DN component recurrences for another uniform class: EVERY connected
ordinary natural graph with three maximal-corner chains and no articulation.
It includes cubes of paths of every length n>=4, not only n=3h, and the
square-path tails described below. Diagrams with more chains remain open.

### The exact shape of this class

Let n be the number of vertices. Since the corners form three chains,
there are n-3 maximal natural corners. A maximal natural clique projects
to distinct chains except for its two corner endpoints, as proved above.
It therefore has at most four vertices. No maximal corner has length one:
such an edge would be the only edge crossing its cut, contradicting the
no-articulation hypothesis. All maximal corners have lengths two or three.

There are n-2 possible tails 0,...,n-3 and n-2 possible heads 2,...,n-1.
The corners use all but one of each. Their tails and heads increase
strictly together. Comparing these ordered lists shows that the length-three
corners occur in one consecutive nonempty range p,...,q, where

    0<=p<=q<=n-4.

Indeed a gap in the head list before a gap in the tail list produces
that range. The opposite order would produce a length-one corner;
coincident gap positions would give consecutive maximal cliques meeting
at only one vertex. More explicitly, if j is the missing tail and h is
the missing head, corner number l has endpoints
l+1_(l>=j) and l+2+1_(l>=h-2). We must have h-2<j; put
p=h-2 and q=j-1. Thus the natural edges are exactly

    ij with j-i<=2,
    and i(i+3) for p<=i<=q.                           (TC1)

Conversely (TC1) has no articulation and exactly three corner chains:
its corners of length two before and after the displayed length-three
range, together with that range, number n-3. Thus (TC1) is an exact
classification, not an extra assumption on the theorem.

### A fixed exchange window sees all three parallel classes

Let L=q-p+1. If L=1 use the four-vertex interval [p,p+3]; if L=2 use
[p,p+4]; if L>=3 use [q-2,q+3]. The induced natural graph is the cube
of a path on respectively four, five or six vertices. Its maximal
corners are maximal in the original diagram as well, and its three
local corner chains belong to the three distinct global chains.

The window contains at least ONE good anchor copy from EACH of the
three global parallel classes. For a six-vertex window, each local
short-edge path has three nodes; either global parity leaves at least
one copy. For a five-vertex window, the middle vertex p+2 is the missing
corner tail and is terminal in its global chain. The two paths involving
it have two nodes, hence one good copy each; the remaining path has
three nodes. For a four-vertex window, p+1 is the missing corner tail
and terminal in its global chain. The normal between the two interior
vertices is therefore good, and one of each pair of shorts of the
retained corner is good. Again all three classes occur.

All flips confined to this interval remain actual in arbitrary exterior:
a forward path testing an edge inside the interval cannot leave it and
return. Such a flip exchanges no global strict edge outside the window.

### The three small window statements

In each window, any two connected states selecting the local maximal
corners, with all these corners covering and the same edge count, lie
in one actual local component. For four vertices this is the proved
tree layer and maximum-corner layer. For six vertices it is the already
proved cube-family result at h=2, including normalization of non-anchor
common-cover states.

For five vertices the tree and maximum layers are again known. Only
the middle layer, with five selected edges, needs an additional argument.
Write M={03,14}. Its four local anchors are

    A=M+{01,23,34},    B=M+{01,24,34},
    C=M+{23,24,34},    D=M+{01,23,24}.

They are connected by the following actual paths:

    B -> A:
      34->13 [14], 24->12 [14],
      12->23 [13], 13->34 [14];
    A -> C:
      23->02 [03], 01->12 [02],
      12->24 [14], 02->23 [03];
    D -> C:
      01->13 [03], 13->34 [14].                        (TC2)

All strict corners remain selected. These ten flips connect all four
anchors, and the general corner-chain preparation connects every
common-cover state to one of them. This proves the five-vertex statement.
Its use is local; no arbitrary five-vertex exterior cover assertion is
being inferred from a small example.

### Transfer occupancies using one selected buffer class

The quotient has three vertices and all three pairs, by the exchange
window. Let their capacities be c_0,c_1,c_2, all positive. An anchor
with occupancy vector m is connected exactly when at least two of its
entries are positive. Let us transfer one selected copy from class i
to class j, where m_i>0 and m_j<c_j. Suppose first that the third class
l has m_l>0.

By unrestricted packing and its inverse, rearrange copies so that the
window contains a selected copy of i, a VACANT copy of j, and a selected
copy of l. This can always be done. If a class has b window slots, the
possible local occupancies range from max(0,m-(c-b)) to min(m,b).
The assumptions give a local occupancy at least one for i,l and at most
b-1 for j. The choices are independent between the three classes.

Remove the chosen i copy and insert the chosen j copy inside the window,
leaving every exterior edge fixed. Before and after, the selected window
is connected: class l joins the third local chain, together with i or j.
Both endpoints are restrictions of global anchors, hence have all local
corners covering. Their edge counts agree. The proved window statement
supplies an actual path between them. It lifts to the original diagram,
so this realizes the desired transfer inside ONE whole source component.

If m_l=0, connectedness forces m_j>0. A transfer which preserves
connectedness must have m_i>=2. Perform instead the three transfers

    i->l, i->j, l->i.                                 (TC3)

Each has a positive third buffer class; the capacity and nonnegativity
conditions hold throughout. Their net effect is the desired i->j.

Finally, all vectors in the capacity box with a fixed total m>=2 and
at least two positive entries are connected by such unit transfers.
Move from a surplus entry toward a deficit entry. The only forbidden
step would leave one positive entry. In that situation the desired
vector, being connected, has a deficit in the third entry; transfer
toward that entry instead. Each step decreases the distance to the
desired vector. Combining this with (TC3) and the window paths proves
that ALL connected anchors in one edge layer lie in one actual component.

### Isolate the whole component and apply NN or DN

For each k=n-1,...,m*, connected common-cover anchors exist by (CQ3),
and the preceding argument connects all of them. Every common-cover
state reaches an anchor by the proved preparation. Thus there is exactly
one connected source component C_k selecting every maximal corner and
having a simultaneous-cover witness. This is uniform in n,p,q.

Every other source component D has an independently smaller expression:
if it omits a maximal corner, delete that corner; if it is disconnected,
reorder its weak blocks; otherwise it has no simultaneous-cover witness
and uses alternating corner deletion. These are the previously proved
whole-component reductions, denoted B_X(D), with X=K,E and identical
integer coefficients. No other unresolved source component is subtracted.

For ANY eligible NN contact in this source, the complete layer identity
therefore gives

    X(C_k)=X(F_k(R))+X(F_(k-1)(R))
                 - sum_(D != C_k) B_X(D).             (TC4)

For an eligible DN contact, it gives

    X(C_k)=X(F_k(R))-sum_(D != C_k) B_X(D).            (TC5)

All sums on the right collect whole components, and all final diagrams
are smaller in the established induction order. The other source
components reduce directly. Below n-1 every source component is
disconnected; above m* none has a simultaneous-cover witness. Hence
these are complete component recurrences in EVERY layer for (TC1),
including unmarked maximal corners and arbitrary strict decorations
permitted by the chosen recurrence.

With only TWO corner chains, there is just one parallel class. The
packing theorem already gives one connected common-cover component
in each feasible layer, so the same full-layer argument applies without
the exchange window. No no-articulation assumption is needed for that
simpler case.

This is an induction step expressed in smaller diagrams. Those diagrams
need not themselves have three chains, so we do not use this family
statement as a substitute for the remaining general theorem.

### Verification and scope

Related Rust: `--three-chain-window` verifies (TC2) and constructs actual
paths between occupancy vectors for all 165 graphs (TC1) on 4..12 vertices.
It replays preparation, local transfer and packing in the full graph.
Only the fixed four-, five- and six-vertex windows use local path lookup;
there is no search through a large source component. Connectedness of
each occupancy layer is checked after every transfer edge has its actual
path certificate. This supplements the unbounded argument above.

The family audit covers 4913 occupancy packets and 1030 layers, checking
12996 transfers by 240283 actual flips; the longest path has 63 flips.
The separate `--three-chain-layer-recurrences` mode checks all smaller
whole corrections in 15 layers of fixed NN and DN examples outside the earlier n=3h
cube family, using the established block/deletion verifier. Sources,
commands, complete logs and hashes are retained with (CS1) in
`crossing-slides-three-chains-20260930/`.

General NN/DN collection for arbitrary diagrams remains UNPROVED. The
new parallel-copy theorem is unrestricted, but the window argument here
uses exactly three global chains and the resulting interval of corners
of length three. With more chains, other chain vertices can occur inside
a proposed window; we cannot assume its local flips are unaffected.
The remaining general problem is transfer between different occupancy
vectors, or direct repair and collection of the actual RHS coefficients.

## Complete diagrams: every connected active layer is one component

2026-09-30 continuation from `1498536`. We settle the complete natural
graph on vertices 0,...,n, n>=2, with its single maximal corner f=0n. This is
a uniform theorem, not another finite check of the five-vertex example.
We use only actual diagram flips and induction on the number of vertices.

**Theorem.** For each k with n<=k<=1+binom(n,2), all connected k-edge
states in which f covers belong to one actual component C_k. Equivalently,
C_k is the unique connected k-edge component active at f. Consequently
every source component in the complete diagram has a whole-component NN
recurrence in smaller diagrams, by the layer subtraction below.

The proof has two steps: produce a chain, then rearrange its extra chords.
We do not claim that a representative has the same valuation as its whole
component. The strict corner remains selected throughout, but may be
redundant at intermediate states.

### Put a chain inside the selected graph

The earlier corner preparation sends a connected state with f covering
to an anchor f+H, where H is a connected graph on 1,...,n. We first show
that actual flips send this anchor to one containing

    P_n={0n,12,23,...,(n-1)n}.                         (CC1)

Remove outgoing cover forks in H: for two covers ab,ac with a<b<c,
flip ab->bc [ac]. The edge bc is absent, and these are actual flips by
the proved fork lemma. The sum of the tails of the selected H-edges
strictly increases, so the process terminates. The cover graph then
has at most one outgoing edge at each vertex. Since it is connected
and increasing, it is a tree directed to its unique sink n. Every
additional selected edge joins a vertex to an ancestor in this tree.

If i<j are children of n, they each have just one outgoing selected
edge, to n. The following four actual flips merge these children:

    in -> 0i [0n],   jn -> 0j [0n],
    0i -> ij [0j],   0j -> jn [0n].                  (CC2)

For the first two flips, removing the child's only outgoing edge leaves
no bypass of 0n. For the third, i has no outgoing edge, so both the
retained 0j and the exchanged shorts cover. The last flip restores
the sole outgoing edge of j. Incoming edges to the children cannot
alter these tests. The endpoint changes only in to ij, and all old
shortcut edges still join ancestors. In particular the rooted-tree
description persists.

The greatest child is n-1. Apply (CC2) until it is the only child.
Then H restricted to 1,...,n-1 is connected. Flip

    (n-1)n -> 0(n-1) [0n].

Inside the smaller complete diagram on 0,...,n-1, we now have an
anchor at 0(n-1). Inductively put its internal chain in place. These
local flips remain actual globally: a forward path testing an edge
inside this interval cannot go out to n and return. At the local
endpoint, the only internal edge from 0 is 0(n-1), while (n-1)n is
absent. Thus 0n covers again, and we reverse the displayed flip.
This proves (CC1), starting with the trivial cases n<=2.

### Use a smaller corner interval without changing the exterior

Call an edge ij with 1<=i<i+1<j<=n a chord. A chain state consists of
P_n and a set of chords. Consider an interval [a,b] of internal vertices.
Open the chain to b by doing, in decreasing j=n-1,...,b,

    j(j+1) -> 0j [0(j+1)].                           (CC3)

Each short is adjacent and covers. Before its flip, the only selected
edges from 0 have heads at least j+1. Afterwards the only new possible
bypass of 0(j+1) would use j(j+1), which was removed. Thus every flip
is actual, irrespective of the chords.

On the ordered subset {0,a,a+1,...,b}, the induced state is a smaller
chain state with corner 0b. Any actual path there lifts globally while
fixing all other edges. For edges whose endpoints lie in [a,b], the
forward-path interval test is immediate. For an edge from 0, no path
can enter a vertex below a: there is no selected edge from 0 to such
a vertex. Edges from 0 outside the subset have heads above b and
cannot return. This remains true throughout the local path.

At another local chain endpoint, undo (CC3) in increasing j. Its cover
tests depend only on edges at or above b, which the local chord changes
did not alter. We have therefore lifted any smaller complete-diagram
chain-to-chain path while restoring the entire exterior.

### Rearrange every chord except 1n

We induct on n. For n>=5, apply the preceding construction to [1,n-1]
and [2,n]. By the induction hypothesis we may rearrange the chords
inside either interval arbitrarily, preserving their number.

Their chord positions together are precisely all positions except 1n.
Their intersection contains 24 when n>=5. Hence the graph on these
positions, joining two positions that lie in one of the two intervals,
is connected. At a fixed number of selected positions, selected/vacant
exchanges along its edges connect all subsets.

For completeness, an exchange between any selected donor and vacant
receiver can be made along a path of positions: perform adjacent
transpositions along the path forwards, then backwards omitting its
last edge. This transposes the two endpoints and fixes the intermediate
positions. Omit any transposition of two equal occupancy bits. Each
remaining exchange is supplied by a smaller interval path. Thus all
chord sets with the same cardinality and the same 1n bit connect.

### Move the remaining bit by a column sweep

Suppose a chain state A omits 1n and selects both 13 and 2n. We give
an actual path to

    A - 13 + 1n.                                     (CC4)

First sweep every selected edge in, i<n, across f in DECREASING i:

    in -> 0i [0n].                                   (CC5)

When we reach i, all larger incoming edges to n have been removed.
Consequently in covers. The existing edges from 0 have heads larger
than i; they cannot reach an unswept incoming tail. This proves that
0n covers before and after the flip and that its new short 0i covers.

Now 01 is absent and 02 is selected. Do 12->01 [02]. Both shorts are
adjacent to the bottom vertex or its successor, and 02 covers: before
the flip no selected edge from 0 has head below 2; afterwards 12 is
absent, so the new 01 cannot give a bypass. Reverse the column sweep,
now including the new 01, in INCREASING i. At each step 0i is the
least remaining edge from 0 and every restored incoming tail is smaller
than i, so both required covers persist. The exact endpoint is

    A - 12 + 1n.                                     (CC6)

Restore the missing chain edge using the selected 13. Open the chain
by (CC3) down to 3. The local graph on 0,1,2,3 has edges 03,13,23
and no 12. Apply (CC2) to its two children 1,2:

    13 -> 01 [03],   23 -> 02 [03],
    01 -> 12 [02],   02 -> 23 [03].

Close (CC3). This restores 12, removes 13, and fixes every other edge,
proving (CC4). Extra chords, including all those to n, are allowed.
The shorter-interval lifting argument verifies their harmlessness during
the four-flip repair.

At chord count c>=2, the preceding rearrangements let us choose an
outer-absent state containing 13 and 2n, provided such a state exists.
If Q=binom(n-1,2) is the number of chord positions, this just requires
2<=c<=Q-1. Formula (CC4) connects the outer-absent and outer-present
families. In the latter, the remaining c-1 chords can again be
rearranged arbitrarily by smaller interval paths.

When c=1, connect the single-chord states 13 and 1n directly. Starting
from P_n+13, open (CC3) down to 2, then do

    13 -> 01 [03],   01 -> 1n [0n],

and close (CC3). With only this one chord, all retained edges in these
two flips cover: the opened chain leaves every vertex 2,...,n with no
internal outgoing edge, so 13 covers and there is no bypass from a spoke
to 3 or n. Removing 13 then leaves 1 with only its edge to 2 until the
new chord is inserted. The path has 2(n-2)+2 flips. At c=0 or c=Q
there is only one chord set. This completes the induction step.

### The fixed five-vertex base

For n<=3 there is at most one chord position. For n=4, the positions
are 13,14,24. We give all the nontrivial connections, so the induction
has no finite-search hypothesis. Start each row at P_4 plus the left
chord set. An entry abc means the actual flip exchanging ab and bc
while retaining ac; its direction is determined by the current state.

| Chord sets | Successive triples |
| --- | --- |
| {13} -> {14} | 034, 023, 013, 014, 023, 034 |
| {14} -> {24} | 034, 124, 014, 023, 012, 023, 034 |
| {13,24} -> {14,24} | 034, 024, 012, 014, 024, 013, 023, 012, 023, 034 |
| {14,24} -> {13,14} | 034, 023, 012, 013, 023, 124, 034 |

The successive graphs check both short and long covers directly; every
row restores P_4 and changes just its stated chord set. Counts zero
and three each have a single state. Together with chain normalization,
this proves the theorem for every n and k in its stated range.

### Collect the whole NN component

Let L be this complete source with strict f=0n, and R its NN target:
delete natural edge 0n and mark 1n strict. Let F_j(R) denote the whole
j-edge layer, itself a union of whole components. For n<=k<=1+binom(n,2),
complete the source layer containing C_k and apply the full NN identity.
Every other component D in that layer already has a smaller expression
B_X(D): disconnected components use the proved weak-block reordering;
connected ones are inactive at f by the theorem and use redundant-corner
deletion. Thus, for X=K,E with IDENTICAL integer coefficients,

    X(C_k)=X(F_k(R))+X(F_(k-1)(R))
                       - sum_(D != C_k) B_X(D).       (CC7)

Every final term is a whole component of a smaller diagram. No unresolved
extra source component is subtracted. Below n edges a state cannot be
connected. Above 1+binom(n,2) the corner cannot cover, by the previous
maximum-layer bound. Those layers reduce directly, so we have complete
component NN recurrences in every layer of every complete source.

This is an induction step, not the full general expansion theorem:
the smaller correction diagrams need not be complete. A complete natural
graph has just one maximal corner, so we do not label (CC7) a general DN
recurrence. DN with overlapping maximal corners remains open outside
the families already proved.

### Verification and remaining scope

Related Rust: the external consumer `dn_joint_span.rs`, modes
`--complete-chain-induction` and `--complete-corner-layers`, reuses the
existing actual-flip model and maintained Graph API. The first constructs
normalization and inductive chord paths and checks every flip in the full
ambient graph. All anchors and all chord subsets are exhausted through
seven vertices; deterministic bounded samples and every chord density
are checked on eight through ten vertices. Only the fixed base with at
most five vertices uses component search, bounded by 512 states. The
induction itself searches only the graph of chord positions, not source
components. The separate layer audit uses the established whole-component
deletion/block verifier on complete sources of three through six vertices.

Sources, exact commands, logs and hashes are retained at
`/lake-cache/ai-projects/requests/VerticalStripLLT/complete-corner-induction-20260930/`.
No Lean build or basis computation is involved. The theorem above is
proved by the written arbitrary-n construction, not extrapolated from
the finite audit.

General NN/DN collection is STILL UNPROVED. We have now settled transfers
between different occupancy vectors for this further unbounded family.
In an arbitrary diagram, a maximal-corner interval is a clique, but its
selected restriction need not be connected. We cannot apply the new local
theorem without its connectedness and corner-cover hypotheses, nor assume
that independently chosen clique paths collect the general RHS image.

## Connected pieces inside a corner interval

2026-09-30 continuation from `56a1931`. The complete-diagram theorem has
a local form that does not require the entire selected interval to be
connected. Let ab be ANY selected natural cover, and let B be the weak
component containing a,b in the restriction of A to [a,b]. Replace the
selected graph on B by any connected graph with the same number of edges
in which ab remains selected and covering. Then the two full states
belong to the same actual component, with every exterior edge restored.

Indeed, B has least vertex a and greatest vertex b, and every pair of
its vertices is natural. Apply the complete-diagram theorem on the
order-compressed set B. A path testing one of its edges cannot leave
[a,b] and return. Inside that interval there are no selected edges
between B and another weak component, and the local path creates none.
Thus every local cover test remains valid globally. No original strict
corner other than ab can lie inside the natural interval ab. All strict
edges are therefore retained. This proves the assertion, even when ab
is normal and other parts of the selected interval are disconnected.

This is a component-membership statement, not a pointwise K/E identity.
It allows arbitrary changes of the connected piece, not just one flip.

## Complete recurrences when the last clique contains every chain terminal

We now prove NN/DN component recurrences for a further unbounded family,
including all powers of ordinary paths. Let the natural graph have N
vertices and maximal corners

    M={0h_0,1h_1,...,ah_a},
    1<=h_0<h_1<...<h_a=N-1.                           (TL1)

Thus every vertex 0,...,a is a corner tail, and no larger vertex is.
Put d=N-a-1. The d corner chains have terminal vertices

    T={a+1,...,N-1}.

They all lie in the last natural clique [a,N-1]. Conversely, if that
clique contains the terminal vertex of every corner chain, all smaller
vertices must be nonterminal, so (TL1) holds. We assume d>=2 below;
for d=1 the natural graph is a path and the full-envelope tree is unique.

**Theorem.** In (TL1), for every N-1<=k<=m*, all connected k-edge
states with a simultaneous-cover witness for M lie in one component C_k.
Every eligible NN or DN contact therefore gives a complete signed
recurrence for each source component in smaller whole components.
Unmarked maximal corners are allowed, with their absent sectors reduced
separately as before.

### Put the required edges into one clique

After corner preparation, an anchor selects M and good normal edges.
Every unordered pair e of corner chains has a good edge joining its two
terminal vertices in T. This is the last copy in that pair's short-edge
path. Consequently the quotient is the complete graph on d vertices,
with positive capacities c_e, and an anchor has occupancies

    0<=m_e<=c_e.

It is connected exactly when its simple support H={e:m_e>0} is connected.
All anchors with fixed m already connect by unrestricted packing.

Suppose we want to transfer one unit from e to f, with m_e>0 and
m_f<c_f. There is a direct construction whenever

    H-f is connected,   and   (H-e)+f is connected.   (TL2)

Deleting an absent edge has no effect in this notation. Pack exactly one
copy of each edge of H-f into T, and no copy of f there. This is feasible:
each positive class supplies one copy, all remaining copies fit outside T,
and the receiver has a vacancy. The selected graph on [a,N-1] is then
the corner a(N-1) plus H-f on T. It is connected and its corner is a leaf
edge. Replacing the terminal copy of e by that of f gives the same
properties by (TL2). The complete-diagram theorem gives actual flips
between these local states. They lift globally since [a,N-1] is an
interval, and it contains no other maximal corner. Pack again afterwards.

This realizes the desired unit transfer between canonical anchors and
retains every original strict edge. The local path may temporarily make
other maximal corners redundant; no step requires those other covers.

### At most one temporary edge removes the two obstructions

We claim that ANY unit transfer e->f whose final occupancy support is
connected is a composite of at most two transfers satisfying (TL2).
If (TL2) already holds there is nothing to prove. Its first condition
fails precisely when f is a bridge of H. Its second can fail only when
e is a bridge and f does not cross the cut of e. In that second case
m_e>=2, since otherwise the required final support would be disconnected.

Choose an absent edge g crossing each bridge cut responsible for these
failures. Such a g exists in the complete quotient. For one cut, d>=3
gives a crossing pair other than the unique selected bridge. (With d=2
there are no distinct donor and receiver classes.) For two cuts, removing
the two bridges gives three connected pieces arranged in a path. Join a
vertex of its first piece to a vertex of its last. This pair crosses
both cuts and was absent. In either case g is different from e,f and
has available capacity.

Perform e->g and then g->f. The first satisfies (TL2): g was absent,
and either H-e is connected or g reconnects the cut of e. If e was a
bridge, m_e>=2, so it remains in the intermediate support. If its last
copy was removed instead, H-e was connected.

For the second transfer, removing f from the intermediate support leaves
a connected graph. This is automatic if f was not a bridge; when f was
a bridge, the new g crosses its cut. If the first transfer removed the
last e, deleting that nonbridge did not disconnect either side of the
f-cut, since H-e was connected. Removing g and adding f also leaves a
connected graph: it restores H, or H-e when the last e was removed.
These are exactly the two conditions (TL2) for g->f. The temporary class
returns to zero and all other occupancies are unchanged.

### Connect the entire fixed-size occupancy layer

Let m and m' have connected support, the same total and the same capacity
bounds. Choose a surplus class e. If removing one unit leaves connected
support, transfer it to any deficit class. Otherwise e is a single-copy
bridge and m'_e=0. Since m' is connected, it contains some edge f crossing
the cut of e. Every such f other than e is absent from the current support,
so it is a deficit class and e->f preserves connectedness.

Each transfer decreases the sum of the absolute occupancy differences
by two. Thus this finite procedure reaches m'. Realize each transfer by
the direct construction or its two-step repair above. Together with
preparation and packing, this proves the theorem's component assertion.

### Collect both recurrences

All other components D in the k-edge source layer have independently
smaller expressions B_X(D): delete a missing maximal corner, reorder weak
blocks if disconnected, or use alternating corner deletion when there is
no simultaneous-cover witness. Therefore the full-layer identities give,
with the same integer coefficients for X=K,E,

    NN: X(C_k)=X(F_k(R))+X(F_(k-1)(R))
                            - sum_(D!=C_k) B_X(D);
    DN: X(C_k)=X(F_k(R))     - sum_(D!=C_k) B_X(D).   (TL3)

All final terms are whole components in smaller diagrams. Below N-1 edges
every component is disconnected; above m* no simultaneous-cover witness
exists. Hence the recurrence covers every layer, not only a dense sector.
The correction diagrams need not satisfy (TL1): this remains an induction
step toward the full theorem, not a replacement for that theorem.

In particular take h_i=i+d, 0<=i<N-d. This is the natural graph with
exactly the edges of lengths at most d, for ANY N>d>=2. Its anchors are
unions of cliques in consecutive blocks of size d, aligned from the right,
with an initial shorter block if needed. The proof permits the resulting
unequal pair capacities. It therefore settles every eligible component
NN/DN recurrence for every ordinary path power, with no divisibility
restriction and with arbitrarily many corner chains.

There is also the order-dual family: the first natural clique contains
the initial vertex of every corner chain. Reverse the order only to
transport the constructed FLIP PATHS, sending a triple (i,j,k) to
(N-1-k,N-1-j,N-1-i). Directed bypasses correspond by path reversal,
so covers and actual flips are preserved. This proves the same uniqueness
assertion in the original diagram, where we then apply its own full-layer
NN/DN identity. We do not assert that order reversal preserves K or E.

### Verification and limits

Related Rust: `dn_joint_span.rs --terminal-clique-transfers` constructs the
paths above on all 120 graphs (TL1) with d>=2 on three through eight vertices,
four larger path powers and one further irregular graph. It checks 2127
occupancy paths: 3892 direct unit transfers and 165 repaired by a temporary
class, giving 4222 local clique paths and 313063 actual flips. Maximum
path length is 6672; graphs have up to 52 natural edges. No global source
component search is used. The only component search is the earlier fixed
five-vertex base of the complete-diagram path constructor.

The separate `--terminal-clique-layers` mode checks complete smaller outputs
for NN on the fourth power of a seven-vertex path and DN with corner heads
[2,4,6] on seven vertices and [3,4,5,7] on eight. In the last DN source,
14 MUST be unmarked: its head is the contact's next vertex, and the new
strict 04 would contain it. The final check includes that absent-corner
sector. Marking 14 strict here is not an eligible recurrence and is not
part of the theorem or final audit.

The general NN/DN problem remains open outside these two families, when
some corner chains terminate before the last clique and some start after
the first clique. The local connected-piece lemma above still
applies, but there need not be one clique containing a good copy of every
chain pair. We have not proved a compatible sequence of local exchanges
for arbitrary overlapping cliques. Nor may we replace such exchanges by
an unrestricted adjacent swap: active membership under that swap fails
already in a complete five-vertex diagram.

### Why the adjacent swap still needs a repair

The last warning has a small exact certificate. In the complete diagram
on 0,...,4 with strict 04, take

    A={02,03,04,12,14,23,24},   sigma=(0 1).

Both 04 and 14 are selected and 01 is absent. The actual flip triples

    012,234,013,234,124,014

send A to {01,02,03,04,12,13,23}, where 04 covers. Thus A is active
at 04. But sigma A lies in an inactive nine-state component. Each of
its states omits 03 and two further edges from the following list:

    {24,34}, {23,34}, {12,34}, {01,34}, {12,23},
    {01,23}, {12,13}, {01,13}, {01,12}.

All other edges of the complete graph are selected. Checking the ten
possible triples in each state gives exactly a connected, closed flip
graph on these nine states. In every one, 04 has the bypass 01,14 if
01 is selected, and otherwise the bypass 02,24. This proves inactivity
and rules out the proposed membership identification even at a leftmost
NN contact and even with just one maximal corner. It does not contradict
the complete-diagram recurrence, which independently reduces the inactive
component instead of identifying it with the active one.

Related Rust: `--complete-swap-audit` checks every such middle state on
three through six vertices and prints this entire certificate. There are
four active-to-inactive failures on five vertices and 110 on six. These
are verified failures of the shortcut, not failures of the recurrence.

The exploratory `--local-clique-anchor-generators` mode checks the positive
connected-piece lemma with actual paths in nine fixed diagrams. Together
with parallel packing, these generators connect every connected occupancy
layer in the eight non-articulation fixtures. The two-K4 articulation
control still has two distinct middle-layer pieces. Restricting retained
edges to maximal corners alone misses even one tree anchor in area 0123434;
normal retained covers (or the separate tree theorem) supply its connection.
This finite generator evidence is not a general connectivity theorem.

The final sources, commands, logs and hashes for these checks and (TL3)
are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/terminal-clique-recurrences-20260930/`.

## Two overlapping cliques: two proved path lemmas

2026-09-30 continuation from `3dec58f`. We consider the natural graph
which is the union of the complete intervals [0,b] and [c,d], where
0<c<b<d. Its maximal corners are f=0b and g=cd. We call a common-cover
state prepared by (P) an anchor. Its two nonsingleton corner chains are
F={0,b} and G={c,d}. In the quotient, the two cliques have common vertices
F,G and the singleton vertices c+1,...,b-1. Only the class FG has capacity
two, with good copies 0c and bd; every other class has capacity one.

The following two path lemmas are proved. We have NOT yet deduced a full
component recurrence for arbitrary two-clique sources from them.

### Introducing the common class

Every connected anchor has an actual path, retaining f and g, to an
anchor containing at least one of 0c,bd. If one is already present,
there is nothing to do. Otherwise 0 is pendant, joined only to b.

We first sweep every selected vd with c<v<d, in decreasing v, to cv
across g. The usual incoming sweep is actual because g covers. After
it, d is pendant, joined only to c. Deleting the two pendant vertices
0,d leaves a connected selected graph on 1,...,d-1. Apply the proved
reachability construction there to make c reach b. Both f and g remain
covers: their pendant endpoints lie outside every constructed triple.

Let I consist of the v with c<=v<b such that vb is selected and c
reaches v. It is nonempty. In decreasing order of I, replace vb by 0v
across f. To check vb covering, any bypass must end in a larger reachable
incoming tail, which has already been swept. After removing vb, v no
longer reaches b for the same reason. Thus each newly introduced 0v
leaves f covering. At the end, c no longer reaches b.

Put p=min I. Then 0p covers. If p>c, take a covering edge tp on a
cover path from c to p, and replace tp by 0t across 0p. No other current
0-neighbor is below p, so 0p covers; t is reachable from c, hence cannot
reach b. Thus f remains a cover. Repeat with p=t. The index strictly
decreases, and the process ends with selected 0c. Throughout, g covers
because it is still the only edge into d.

Finally apply preparation (P). It keeps every already-good edge,
including 0c, and returns to an anchor. This proves the assertion with
no component enumeration or assumption about its size.

Related Rust: `dn_joint_span.rs --two-clique-bridge` checks all 84
parameter choices on four through ten vertices, exhaustively over
anchors through six vertices and with 128 deterministic bit samples per
larger graph. The 1870 connected sampled anchors missing both copies
produce 14534 checked actual flips, with maximum path length 24 and up
to 44 natural edges. Every path retains both corners, preserves its edge
count, and ends in a good anchor containing 0c. These are finite checks
of the explicit construction, not evidence substituted for its proof.

### Isolating a core and restoring its exterior

Let U={0,...,b} union {d}. Suppose the selected restriction of an anchor
to U is connected. We may replace that restriction by ANY connected
anchor of the same edge count on U, leaving every exterior selected
edge exactly as before, along an actual path retaining f and g.

After order compression, the induced natural graph on U has corners
0b,cd whose heads are its last two vertices. Order reversal puts it in
the proved terminal-clique family. Thus any two connected common-cover
anchors of the same size on U have a local actual path retaining the
corners. Reversal is used only for this path statement, not for K or E.

To lift this path, first sweep selected vd with b<v<d to cv across g,
in decreasing v. No omitted vertex now has an edge into d. A forward
path that leaves U cannot return: its only possible return vertex is d.
Therefore all internal cover tests are unchanged by the exterior, and
the entire local path lifts.

At its endpoint, the new restriction is an anchor, so c has no internal
outgoing edge except cd. Undo the sweep in increasing v, replacing cv
by vd across cd. At each undo, remaining c-neighbors from the sweep are
larger than v, and already restored incoming d-tails are smaller than v.
Hence cv and cd cover, and vd is absent. The flip is actual. All swept
edges return to their original positions. This proves the local
replacement assertion, including exact restoration of the exterior.

This proof uses the terminal-clique path theorem; this turn's Rust mode
checks the first lemma only. Neither lemma identifies individual states'
K/E values: they assert membership in the same actual component.

### Remaining two-clique argument, not yet proved

A possible completion is to reach an anchor containing the quotient
star centered at F. Once this is done, the free positions are the
nonstar classes in the two cliques and the second FG copy. The two sets
of free positions overlap in that extra FG position. Fixed-count
rearrangements within each set would connect all global fixed-count
choices. The core lemma supplies the left rearrangements. The terminal
clique construction suggests the right ones, with packing used to place
the FG copies. The complete assembly has not been checked or promoted
to a theorem.

For recovery, the proposed star construction is as follows. First use
the proved introduction lemma and crossing slide to select bd. In the
right-hand component containing cd, use the complete-cover theorem to
make the terminal vertices a star at b, with arbitrary extra edges to
preserve the count and with c pendant. In each other right-hand
component, make its intersection with [c+1,b] connected inside that
interval. One suggested construction applies the reachability lemma
from the least intersection vertex to the others. Its hull-removing
moves above b do not remove internal intersection edges, and subsequent
moves inside the interval preserve its weak blocks. These assertions
need to be checked in the complete construction.

If 0c is absent, move bd to 0c by the crossing slide. Then every right
component should meet only one selected left component. Global
connectedness would force the whole left restriction connected. Apply
the complete-cover theorem in [0,b], with f retained, to obtain 0c and
all ib for 1<=i<b, i!=c, with extra good edges preserving the count.
Move 0c to bd if needed. The right restriction should now be connected;
normalize it with retained cd to a star at b on its terminal vertices.
At that point the quotient star is selected.

Still verify every intermediate cover, retained corner, connectivity
assertion and endpoint anchor condition, then the free-position
rearrangements. Do not use this plan to assert common-cover uniqueness
or subtract extra source components yet. The articulation case c=b
has separate product components and is instead covered by the
[right-marked attachment theorem](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#full-layer-recurrences-preserve-the-right-endpoint).

## Complete component recurrences for two overlapping cliques

The candidate in the preceding section can now be completed. We keep
0<c<b<d and M={0b,cd}. We prove that all connected common-cover states
of a fixed size lie in one actual component retaining M. As before,
this implies the whole-component recurrence by full-layer subtraction.
The articulation case c=b is excluded.

### Reaching a star

We first apply (P) and the common-class introduction lemma. By crossing
transport we may assume bd selected. Consider the restriction to the
right clique [c,d]. Its connected block B containing cd also contains b.
Use the complete-cover theorem on B, retaining cd, to select every edge
joining b to B minus {b,c}. Choose the remaining edges among pairs of
vertices in B minus {c}, preserving the local count. This is possible:
the original anchor had c joined only to d, so its count is at most one
plus the number of those pairs; connectedness gives the required lower
bound. The endpoint is again an anchor, with c pendant in B.

Every other right block meets S=[c+1,b]. Otherwise it has no selected
edge to the left clique and contradicts global connectedness. Let a be
its least vertex in S. For each other v in its intersection with S, use
the reachability construction inside that block to make a reach v.
These paths can be chosen without destroying the connections in S that
have already been made. Indeed a is also the least vertex of the block,
since every vertex outside S is greater than b. The hull-removing steps
above b remove only edges incident with a vertex above b, and thus no
edge internal to S. Once the hull is inside S, all flips preserve the
weak blocks of the restriction to S. The final normalization on [a,v]
has the same property. Therefore the entire intersection with S becomes
connected inside S. All these vertices are corner-chain terminals, so
all introduced edges are good; we remain at an anchor.

If 0c is absent, use reverse crossing transport to replace bd by 0c.
Now the left restriction [0,b] is connected. To see this, the former
right block B has its intersection with [0,b] connected in the left
restriction: its terminal intersection is joined to b by the selected
star, and c is joined to b by 0c,0b. Every other right block has its
intersection connected by the preceding construction. Removing bd may
split B, but every resulting piece meets this same left component.
All other right blocks also meet just one left component. If there
were two left components, the right restriction could not join them,
contradicting global connectedness.

Use the complete-cover theorem in [0,b], retaining 0b, to reach the
spanning tree consisting of 0b,0c and all ib with 1<=i<b, i!=c, together
with enough extra good edges to preserve the count. There are enough
good positions because the starting restriction was an anchor. The
required tree lies among these positions. The endpoint is an anchor.
If bd is absent, replace 0c by bd using crossing transport.

The right restriction is now connected. Each former block other than B
meets S, all vertices of S are joined to b by the newly selected edges,
and cd,bd join c,d to b. The former B's remaining terminal vertices are
also connected to b by its star. No other right-block edge was changed
by the left-clique path. Apply the complete-cover theorem to the whole
right clique, retaining cd, and select its terminal star centered at b,
with extra good edges to preserve the count. The left-exclusive star
edges stay fixed.

We have reached an anchor containing the fixed tree

    T = {0b,cd} union {bv : 1<=v<=d, v not in {b,c}},     (TC1)

where bv denotes the increasingly ordered pair. Every indicated pair
is natural and good. In the corner-chain quotient this is the star at
F, with the FG edge represented by bd. Every path used above retains
both original corners, even when another corner temporarily ceases
to cover. Its endpoints have all corners covering.

### Rearranging the extra edges

Let P be the good positions outside T. They are the nonstar quotient
edges, each of capacity one, together with the extra FG position 0c.
Write P_L for those supported on U={0,...,b} union {d}, and P_R for
those in the right terminal clique [c+1,d], together with 0c. Then

    P = P_L union P_R,       0c in P_L intersection P_R. (TC2)

The quotient is the union of two complete cliques, so these are all
positions. We can perform any fixed-count rearrangement within either
set, fixing the other positions and keeping T at the endpoints.

For P_L use the proved core-isolation lemma. Both core restrictions
are connected because they contain T restricted to U; they are anchors
of the same size. Every exterior edge is restored exactly.

For P_R use the terminal-clique transfer construction on its quotient
clique, whose terminals are c+1,...,d. The FG class has capacity two
and every other class capacity one. Each class has a good copy joining
its terminals; the only copy outside the clique is 0c. Packing that
class uses crossing transport across 0b,cd and restores all other
edges. The connected-support transfer argument from (TL1)--(TL3)
therefore applies verbatim: pack the support minus the receiver into
the terminal clique, use its complete-cover path with attached cd,
then restore packing. When the direct connectedness conditions fail,
use the absent temporary class across the required bridge cuts. These
are the already-proved arbitrary-capacity conditions, not a new
assumption about this graph. All local paths lie in [c,d], so they
cannot change 0b or any left-exclusive edge. The shared corners stay
selected during the packing paths as well. At the requested endpoints
T is selected; the intermediate support need only stay connected.

For completeness, (TC2) makes these moves sufficient for any prescribed
fixed-size subset of P. Swap a selected unwanted position with a missing
wanted one. If both belong to one of P_L,P_R, use its rearrangement.
Otherwise use h=0c as the intermediary. If h is absent, move the unwanted
position to h and then h to the wanted position. If h is present, move
h to the wanted position and then the unwanted position to h. In either
case h returns to its original status, and both steps take place within
one of P_L,P_R. Thus all anchors containing T with a given edge count
are in one actual component. Together with the star construction, this
proves the common-cover uniqueness assertion for all sizes.

### Whole-component consequence and checks

Every connected common-cover state first reaches an anchor by (P), so
there is exactly one component C_k containing such states in each
feasible layer n-1<=k<=|A*|. This assertion concerns the actual component,
including its states where a corner is redundant. Every other source
component reduces independently by an absent corner, a disconnected
weak-block correction, or alternating corner deletion. Below n-1
all states are disconnected; above |A*| none has all corners covering.

For any eligible NN contact on this two-clique source, the ordinary
full-layer identity therefore gives X_(C_k) as the sum of whole target
components in layers k and k-1, minus the proved smaller whole-source
corrections. The identical signed formula holds for K and E. All output
diagrams are smaller in the established induction order. The right-marked
version and arbitrary right attachments follow from (RE2)--(RE3).

This settles every component for a two-overlapping-clique source. Such a
source has two crossing maximal corners with different endpoints; it is
not an arbitrary direct DN source with two touching strict corners.
General NN/DN collection for more complicated clique overlaps remains
unfinished. The separate articulation case is handled as products, and
is not included in the uniqueness assertion.

Related Rust: `dn_joint_span.rs --two-clique-star` checks the complete
star construction on all 84 parameter choices on four through ten
vertices, exhaustively over connected anchors through six and with 128
deterministic samples per larger graph. All 8129 applicable paths pass:
3382342 actual flips, maximum length 3190, up to 44 natural edges.
Every flip is checked globally, every corner remains selected, and every
endpoint is a good anchor containing (TC1). There is no global component
search in this mode; the complete-cover constructor retains its fixed
five-vertex base search. The abstract final rearrangement proof above
uses the already-verified terminal-clique construction and the proved
core-isolation lemma; this mode does not claim to execute that final
rearrangement.

The separate `--two-clique-layers --right-marked-layers` mode checks the
full recurrence at the first corner for (d+1,b,c)=(6,3,2),(7,4,2),(7,4,3).
All 17 feasible source layers pass: 25804 survivor states, 1773 whole
target components with 38107 states, 676 disconnected corrections with
6003 states, and 783 alternating source corrections with 6300 states.
The latter produce 3353 whole deletion terms. There are 3058 positive
and 2744 negative terms, and 18900 checked redundancy witnesses. Every
signed right-marked fibre identity and smaller-diagram assertion passes.
These checks include the whole components, not only their anchors.

Frozen sources, commands, logs and hashes for these two modes are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/two-clique-recurrences-20260930/`.
No Lean build, coloring enumeration or basis calculation was used.

## A three-corner family with a complete DN recurrence

The [DN continuation](COMPONENT_DN_JOINT_REPAIRS.md#a-uniform-three-corner-dn-component-recurrence)
proves common-cover component uniqueness and a full DN recurrence for
maximal corners 0a,1(a+1),ae, with a>=2 and e>=a+2. Its anchors are two
complete quotient graphs meeting at two vertices, with one copy of the
shared edge in each graph. Complete-cover paths rearrange a connected
side; crossing transport moves the shared edge between sides. At most
two preparatory transfers make both sides connected in a cyclic layer,
and subsequent transfers connect all allocations. The fixed-envelope
tree theorem handles the tree layer. This supplies the whole-component
subtraction, not merely a conditional local path. A middle corner 1c
with c>a+1 introduces additional cross edges and remains outside this
new theorem.

## Pendant inheritance of common-cover uniqueness

2026-09-30 continuation from `b7c4863`. The following reduction concerns
ACTUAL PATHS and common-cover component uniqueness. It is not a deletion
identity for the value of a whole component.

Let the first two maximal natural corners of a connected ordinary graph
be 0a and 1b, with a<b. Write r(v) for the terminal vertex of the corner
chain containing v. Assume

    r(v) < r(0) for every 0<v<a.                        (PI1)

In particular, (PI1) holds if the corner chain beginning at 0 ends at
the last vertex. Delete vertex 0, keeping the induced order, and call
the resulting natural graph G'. If all connected common-cover states
of each size in G' belong to one actual component retaining its maximal
corners, then the same assertion holds in G.

To prove this, prepare any connected common-cover state by (P). The
normal edges 0v with v<a have the wrong chain-label order by (PI1), so
none occurs in the prepared anchor. Its only edge at 0 is 0a. Deleting
this pendant vertex leaves a connected selected relation of one fewer
edge. Moreover, the maximal corners of G' are exactly the old ones
other than 0a: every remaining edge of the first natural clique is
contained in the next clique [1,b]. No new maximal corner is introduced.
The remaining corners still cover. Their chain terminals are unchanged.

Prepare two source states of equal size. Their restrictions to G' have
equal size and lie in the same component by hypothesis. Lift an actual
path between them by keeping 0a selected and all other 0-edges absent.
A directed cover test with endpoints at least 1 cannot visit 0. Hence
every local flip lifts, and 0a stays selected and covering. Concatenate
with the preparation paths and the reverse preparation of the second
state. This proves the asserted uniqueness in the original graph.

There is an order-dual version. Reverse the diagram, use the preceding
argument, and reverse only the constructed paths back. In particular,
if the last two maximal heads are consecutive and the corner chain
ending at the last vertex starts at 0, the last vertex can be peeled
in a reversed preparation. This does not assert order-reversal invariance
of K or E. Once uniqueness is obtained, use the original diagram's own
full-layer NN/DN identity and its smaller whole-component corrections.

The fixed-leaf image need not itself be a whole source component. For
example, with maximal corners 02,13,24, the anchor {02,13,24,12} has 0
pendant. The actual 012 flip sends it to {02,13,24,01}, which does not.
Thus we do not identify a whole source component with its pendant
restriction or multiply a smaller component value by a leaf factor.
The deduction of a recurrence still uses common-cover uniqueness and
full-layer subtraction, after independently reducing every extra source
component.

The [longer-middle DN application](COMPONENT_DN_JOINT_REPAIRS.md#all-middle-lengths-in-the-three-corner-dn-family)
uses the proved two-clique theorem as the smaller-graph input. It removes
the middle-length restriction from the preceding DN family without
constructing new cross-edge transfers.

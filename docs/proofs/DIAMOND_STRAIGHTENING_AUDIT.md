# Diamond straightening: obstruction and an auxiliary-state repair

This is a mathematical audit, not a Lean completion claim. The fixed-diagram
straightening proposal in `FLIP_COMPONENT_INDUCTION.md` is false. A short
repair of its first obstruction suggests a more flexible uniform lemma using
auxiliary posets, diamond identities, and HRV-preserving swaps. The full
component conjecture remains open.

## A general obstruction to retaining the original strict graph

Let the weak connected components of the strict graph have vertex sizes
s_1,...,s_k. In every orientation whose reachability poset is a disjoint union
of chains, each strict component lies entirely inside one of these chains.
Consequently the chain-size partition is obtained by grouping the s_i and
adding sizes inside each group.

For such a chain-poset orientation the HRV fibers are exactly its chains:
each chain has one sink, and a greatest reachable lift must end at a sink.
This also applies to circular diagrams with winding chains. Therefore the
HRV expressions of chain-poset states lie in the span of h_lambda for these
grouped-size partitions only.

If a complete component has a nonzero coefficient of h_mu for a partition mu
outside this list, its sum cannot be equivalent to a combination of these
chain states under ANY relations preserving the HRV expression. This excludes
signed rational coefficients and nonzero integer multiples as well. It is
not just an obstruction to a particular greedy diamond algorithm.

## Exact obstruction

Use one-based labels, the ordinary area sequence (0,1,2,2), and strict edges
13 and 24. These are permitted corners. The normal edges are 12,23,34;
write their membership as three bits in that order. Every selection is
admissible. The only possible flip triangles are 123 and 234.

The complete one-ascent component is

    C = {100,010,001}.

Its HRV partitions, in the displayed order, are (3,1), (2,2), and (4), hence

    H_C = h_(3,1) + h_(2,2) + h_4.

The only chain-poset states are 000 and 111, with partitions (2,2) and (4).
The h_(3,1) term already proves that fixed-diagram straightening is impossible.
The strict components have sizes 2,2, so this also instantiates the general
obstruction above. This is not a counterexample to the component identity.

For an independent algebraic certificate, all diamond relations are

    100 + 010 = 000 + 110,
    101 + 011 = 001 + 111,
    010 + 001 = 000 + 011,
    110 + 101 = 100 + 111.

The linear functional taking value 1 on 100 and 110 and zero on the other
six states annihilates every relation and both chain states, but takes value
1 on C. Thus even arbitrary signed diamond combinations cannot suffice.
There are no extra circular flips in this ordinary diagram: all edges move
forward across its zero-area cut, and the missing edge 14 cannot be a cover.

## Repair by one auxiliary diamond and a swap

Name the states

    U=100, N=010, W=001, M=101, B=000, F=111.

The first and fourth diamond relations imply

    X_N + X_M = X_B + X_F,          X in {K,H}.

Introduce two auxiliary posets

    J = (1<2<4) disjoint union {3},
    R = transitive closure of {12,24,34}.

Both omit an original strict edge. The diamond on 1<3<4, based at J, uses
1<4, which is already implied by 1<2<4. It gives

    X_U + X_R = X_J + X_M.

Swapping vertices 2 and 3 maps R to W. This preserves the order-enumerator
via color relabeling. Both have a unique sink 4, so it also preserves the HRV
partition (4). Consequently

    X_U + X_N + X_W = X_J + X_B + X_F,     X in {K,H}.

All three right-hand posets are disjoint unions of chains, of sizes (3,1),
(2,2), and (4). This is a simultaneous coloring/HRV certificate for the
component identity, using two original diamonds, one auxiliary diamond,
and one justified swap. No inference from H alone is involved.

The point of this calculation is to identify the extra move required by a
uniform proof. Merely adjoining a redundant edge 14 while retaining strict
13 and 24 cannot create a chain state of type (3,1).

## Uniform overlap identity with symmetric exterior

Here is a reusable statement with explicit hypotheses. Let a<b<c<d be four
vertices, and let E be an arbitrary fixed exterior directed relation. Use
transitive closures of the following selected relations:

    B = E + ac + bd,
    U = B + ab,           N = B + bc,       W = B + cd,
    V = B + ab + bc,      M = B + ab + cd,
    F = B + ab + bc + cd,
    J = E + ab + bd,      R = J + cd.

In the ordinary case assume all edges of E point forward. Let sigma swap b,c
and fix other vertices, and suppose sigma(E)=E. Then for both the weak order
enumerator K and the HRV expression H,

    X_U + X_N + X_W = X_J + X_B + X_F.       (*)

Proof: the diamond on abc gives U+N=B+V. The diamond on bcd gives
V+M=U+F. Subtract to obtain N+M=B+F. The auxiliary diamond on acd uses the
relation a<d already implied in J, giving U+R=J+M.
The exterior symmetry identifies R and W under sigma.

For the HRV part of this last identification, b and c both have outgoing
edges to d in R and W. They are not sinks. The swap therefore fixes every
sink and conjugates reachability; the largest reachable sink, and hence
all HRV fiber sizes, is preserved. This argument allows arbitrary exterior
sinks and does not require b,c to be adjacent. The K part is the ordinary
bijection which permutes the vertex colors. Combining the identities gives (*).

A circular version has the following sufficient hypotheses: choose lifts
in one period a<b<c<d<a+n; use the periodic swap exchanging b+kn with c+kn;
require invariance of the ACTUAL integer lifted exterior relation under this
swap; and require projected acyclicity of F. All the other selected states
are subsets of F, so they are admissible. Projected acyclicity is essential;
acyclicity of a positive integer graph alone does not exclude a circular loop.
The swap fixes every integer sink, and the same maximum argument applies.
The usual periodic diamond proof uses first occurrence of an added edge and
admissibility to prevent return to another lift of its tail.

This is a uniform simultaneous valuation identity, independently audited by
Astra. It is not yet a uniform component-reduction theorem:

- Exterior symmetry is a hypothesis to establish, not a consequence of the
  four displayed vertices.
- U,N,W need not be the entire global flip component in the presence of E.
- J,B,F need not be chain-poset bases with arbitrary exterior relations.

## Asymmetric exterior: an explicit correction which can cancel

We can remove the exterior-symmetry premise from the local calculation by
retaining a correction. Write sigma E for the image exterior relation.
The swap sends R(E) to W(sigma E), so

    X_U(E) + X_N(E) + X_W(E)
      = X_J(E) + X_B(E) + X_F(E)
        + X_W(E) − X_W(sigma E),          X in {K,H}.

The conjugated relation sigma E may fail to be naturally increasing or to
belong to a valid circular diagram. We use it only as an auxiliary poset or
periodic reachability relation. Its finite projected order is acyclic by
conjugacy. Its reachable sets on the integer cover are images of the original
finite reachable sets, so maxima exist.

For HRV preservation, more than abstract poset isomorphism is used. Every
moved vertex b+kn or c+kn in R(E) reaches the fixed higher vertex d+kn.
Thus none of the moved vertices can be a reachable maximum. After swapping,
any moved reachable vertex is still below that same reachable d+kn. All
possible maxima are fixed, so the actual maximum and its fiber cardinality
are transported correctly. The coloring enumerator is preserved by relabeling.

For a finite collection of exterior states stable under sigma, with integer
multiplicity m(E)=m(sigma E), summing the correction yields zero by reindexing.
This gives a more concrete global target than unrestricted straightening:

1. Express a labeled complete source-component sum, using valid simultaneous
   identities and independently known terms, as a combination of the displayed
   three-state packets.
2. Prove that their exterior multiplicities are invariant under the swap.
3. Reduce or evaluate the remaining J,B,F packets with a justified induction.

None of these three steps follows just from the local calculation. In
particular, a source component need not initially be a union of whole
three-state packets. Retaining the original component label is essential;
otherwise cancellation might only prove a sum of two unknown component
identities. This is the precise next overlap-completion problem.

## Formalization boundary and next proof search

`Circular/HRVTriangle.lean` already proves `Diagram.tri_local_identity`,
including zero contributions for inadmissible selections. Its long edge is
required to be strict. A global flip supplies a common SELECTED long edge,
which can instead be normal. A useful bounded extension would replace the
strict-edge premise by membership in the common selected base. The existing
`orientMono_noop`, first-use decomposition and maximum comparisons should
support it. The coloring diamond has the elementary indicator proof in the
preceding research note.

For all four states of a genuine flip, base admissibility follows by
monotonicity. A cycle in the full state can be reduced to a cycle in a middle
state or in the base by replacing the two short steps by the common long
step. This argument should be formalized on projected edge instances, so
periodic translates are handled correctly.

The strategic target is now diamond straightening with auxiliary states and
certified swaps. A normalization theorem confined to the original diagram
and strict graph should not be pursued. The next substantive question is
how asymmetric exterior contributions cancel or move between labeled source
components. An arbitrary poset isomorphism cannot be assumed to preserve
HRV; its action on reachable maxima must be proved.

## Checks and provenance

Primary independently found the obstruction with an exact sparse rational
span probe; Astra independently derived the strict-matching certificate by
hand and supplied the auxiliary-state repair. Terra audited the existing
Lean HRV diamond and four-state admissibility gap. No worker ran a Lean
build, no new Lean theorem is claimed, and no Overleaf files were edited.

The one-off probe was justified after the Rust capability audit: existing
LLT/HRV and linear-algebra APIs do not expose circular flips or their diamond
relation module. The probe enumerates finite selected graphs, uses full
lifted covers, and checks its separating functional exactly. It generated
no polynomial family and is not a new reusable library implementation.
It checked the specified eight-state witness; no large-range theorem is
inferred from the initial search.

External directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`.
The self-contained algebraic certificate above is authoritative for the
negative claim. The probe and JSON receipt have SHA256 hashes:

- `probe.py`: `6f4517aca6cfdfa5b802a05edc5ffef24fb245a9ab568d5c5b0abadde4494db4`;
- `strict-matching-certificate.json`:
  `d86719a8021ca47442df41dfb247b972ee43e8e5796ae91cd2e28dd4fa596c65`.

An additional probe allowing ordinary auxiliary forward posets and identical
transitive closures still left a nonzero residual. It did not include the
HRV-preserving swap used above and is not evidence against the repaired route.

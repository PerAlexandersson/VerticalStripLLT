# Component packets for the ordinary bounce recurrences

2026-09-28. We return to the component recurrence requested by the author.
The ordinary NN packet recurrence below is proved mathematically and has an
independent Luna audit. The DN reconstruction was proved in the
[DN completion note](DN_COMPONENT_COMPLETION.md). We also give a counterexample
to its unqualified isolation conjecture, a proved invariant of its packets,
and a more precise remaining question. These are research results toward a
combinatorial proof; they do not replace the completed manuscript argument.
The [DD continuation](COMPONENT_DD_PACKETS.md) extends the packet argument
to eligible ordinary DD steps and supplies a common decreasing measure.

The author's subsequent clarification prioritizes a direct recurrence for
one component: split its orientations, redistribute with diamonds, and
reassemble complete smaller components using the same coefficients for K
and E. Packet isolation below is only a sufficient alternative; it must not
be imposed as an additional requirement on that direct construction.
See the [direct NN redistribution](COMPONENT_NN_REDISTRIBUTION.md) for the
resulting one-component split, a complete example, and exact Rust certificates.

Throughout, K is the strict-coloring enumerator and E is the HRV elementary
expression. We use ordinary diagrams, so every selected relation is acyclic.
All component sums are unweighted. Their common ascent weights can be restored
after the component identities are established.

## The increasing forests of Abreu--Nigro

The forests in our [diamond reduction](COMPONENT_AUXILIARY_DIAMONDS.md) are
the increasing forests used by A. Abreu and A. Nigro: each nonroot vertex has
one smaller parent. Their
[forest paper](https://arxiv.org/abs/2006.08418), Proposition 3.4, proves the
modular law by pairing permutations under an adjacent transposition.
Proposition 3.5 gives a complete-graph recurrence by separating the tree
containing the least vertex. Their orientation-to-forest map in Corollary 4.2
preserves the lowest-reaching partition and has explicitly weighted fibers;
reversing the vertex order gives the corresponding highest-reaching convention.

Their forest partition records tree sizes. It is not the HRV partition of
the same forest directed toward larger children: the increasing tree with
edges 12,13 has tree-size partition (3), but its forward HRV partition is
(2,1). The orientation convention matters when comparing the constructions.

These statements concern the whole graph. A flip can change the HRV
partition, so those forest fibers cannot themselves be unions of complete
flip components. The useful question is whether the recurrence can be refined
to sums over components. We prove such a refinement for explicit packets of
components below; isolating an individual component is a separate step.

Related source: [the modular-law paper](https://arxiv.org/abs/2006.00657).
The local cache contains versions 2006.08418v1 and 2006.00657v2, paper IDs
493 and 494, with source packages and extracted text.

## An NN recurrence in complete component sums

Let L be an ordinary eligible NN diagram, with strict corner ac and b=a+1.
We retain the full first-bounce hypotheses: ac has length at least two,
the boundary values at a and b agree, neither a nor b is a strict head,
and the area decreases immediately after c. Let R be the diagram obtained
by shortening ac to bc. Put q=ab and r=bc. In L both q,r are normal; in R,
r is strict and q is normal.

Let B be the common exterior normal set, and let σ exchange a and b.
The NN geometry makes Q↦σQ an involution on subsets of B and fixes the
other strict edges. For Q⊆B, write L_ij(Q) for the source state with q
selected when i=1 and r selected when j=1. Write R_i(Q) for the target state
with q selected when i=1. The strict edges are included in these states.

For either X=K or X=E, the local identities are

    X(L_10(Q))+X(L_01(Q)) = X(L_00(Q))+X(L_11(Q)),
    X(L_00(Q)) = X(R_0(σQ)),
    X(L_11(Q)) = X(R_1(Q)).                         (1)

For K, the first identity follows by partitioning colorings according to
the two short inequalities. Under c(a)<c(c), at least one of
c(a)<c(b) and c(b)<c(c) holds; their intersection imposes both.
The second identity relabels vertices, and the third removes the redundant
edge ac. For E, these are the established HRV diamond, bottom swap, and
top closure identities.

We define an auxiliary graph J_NN whose vertices are the complete source
components. Brackets denote the component containing a state. Its edges are:

1. [L_10(Q)] joined to [L_01(Q)] for every Q.
2. For every actual target flip R_0(Q)↔R_1(P), the two joins

       [L_00(σQ)] -- [L_01(P)],
       [L_01(σQ)] -- [L_11(P)].

These are imposed joins between components, not assertions that their
displayed representatives are source flip neighbors.

**NN reconstruction.** Let h be any integer multiplicity on source states
which is constant on each connected class of J_NN. Put
α(Q)=h(L_01(Q)). Then the target multiplicities

    g(R_0(Q)) = h(L_00(σQ))+α(σQ),
    g(R_1(Q)) = h(L_11(Q))+α(Q)                    (2)

are constant on complete target components. Moreover,

    Σ_A h(A) X(A) = Σ_T g(T) X(T),    X=K,E.       (3)

We first verify target-component constancy, including exterior flips.
For a target flip preserving q=0, swap conjugacy gives the corresponding
source L_00 flip. This also lifts to L_01 by adding r. Indeed, r has no
proper containing natural edge except ac, by the terminal area gap; and
an alternate a-to-c path through r would need an a-to-b path. The latter
is impossible without q because a,b are adjacent. Both summands in the
first line of (2) are therefore constant on this target flip.

For a target flip preserving q=1, add ac to obtain the source L_11 flip.
The added edge is redundant through ab,bc; it is also a maximal corner, so
it cannot enter a path testing another natural-edge cover. Now delete q
to get the corresponding L_01 flip. It is not exchanged by this flip,
and its length one prevents it from being a retained long edge. Deleting
it preserves the required covers at both endpoints. Both summands in the
second line of (2) are therefore constant.

Finally, for R_0(Q)↔R_1(P), the two defining joins give

    h(L_00(σQ))=α(P),       α(σQ)=h(L_11(P)).

Their sums are the two sides of (2). This proves constancy across every
target flip, hence on every complete target component.

The middle joins give h(L_10(Q))=h(L_01(Q))=α(Q). Apply the diamond in
(1) with coefficient α(Q), transport the bottom and top terms, and reindex
the bottom sum by σ. The resulting coefficients are exactly (2), proving
(3) simultaneously for K and E.

Each edge of J_NN preserves the source normal-edge count. For a mixed target
flip, |Q|=|P|+1, which verifies both displayed joins. A source class at ascent
k may give target components at ascents k and k-1. If h is a single class
indicator, the two summands defining each g have different source ascents,
so at most one contributes. Thus g is the indicator of a union of complete
target components. There is an explicit bijection on the state occurrences:

| Source state | Target state |
|---|---|
| L_00(Q) | R_0(σQ) |
| L_01(Q) | R_0(σQ) |
| L_10(Q) | R_1(Q) |
| L_11(Q) | R_1(Q) |

Rows with the same target have different source ascents, so they cannot both
occur in the class. The two middle rows preserve the sum of the valuations
by their diamond, rather than preserving each valuation state by state.
The target's doubled area is two less
than the source's, so all its components are available to area induction.

This is an actual recurrence in whole component sums. Applying it to one
component requires removing or separating any other source components in
its J_NN class.

Related Lean: `Circular/FirstBounceOrientationMatching.lean`,
`nn_match_bottom`, `nn_match_top`, and `nn_swap_step`;
`FirstBounceOrientationIdentity.lean`, `nn_local_identity`. The new
component reconstruction and its flip lifts are mathematical proofs, not
new Lean declarations. The ordinary hypothesis is essential to the present
argument: a circular L_01 state can be inadmissible even when L_00 is valid.

## Why DN isolation needs the other reductions

The assertion that every DN completion class contains at most one component
active at its distinguished corner is false. Here is a hand-checkable
counterexample, using labels 0,...,6:

    area = (0,1,2,3,3,4,3),
    strict edges = {03,15,36},
    e=03, f=36, q=34, r=46.

We display normal selections only. Two complete source components are

    C: {02,24} -- {23,24} -- {24,34} -- {24,46},
    D: {02,34}, {23,34}, {02,46}, {23,46}.

The three flips in C use triangles 023,234,346. The component D is the
square of the independent flips 02↔23 and 34↔46. Inspection of the selected
long edges gives no additional flips. Every state is a forest, hence every
strict corner is a cover; in particular both components are f-active.

The target has strict edges {04,15,46}. Its two states R_10({02}) and
R_10({24}) are joined by the actual 024 flip, retaining 04. The target-middle
rule of the DN completion graph joins [L_01({02})]=D to [L_01({24})]=C.
Thus C and D lie in one completion class.

Both have weak vertex blocks {0,2,3,4,6} and {1,5}. They can be handled by
vertex factorization before using DN. On the large block their selected-edge
envelopes differ: C has maximal intervals 03,24,36, while D has 03,36.
The new target corner 04 contains 24 and removes that distinction. This
explains why a recurrence using the global envelope can merge them.

## The weak blocks of NN and DN packets are fixed

For every NN or DN completion class, the weak vertex partition and the number of
selected edges in each block are invariant. In particular, the class is
either connected throughout or disconnected throughout.

For NN, the middle join replaces the two-edge tree {ac,ab} by {ac,bc}.
Both connect a,b,c, so adjoining the same exterior preserves the partition
and edge count in each block. For a mixed target flip R_0(Q)↔R_1(P), these
three vertices lie in one block at both endpoints, since R_1 contains ab,bc
and flips preserve weak blocks. L_00(σQ) is the swap of R_0(Q), with a,b in
one block; L_01(P) replaces {ab,bc} by {ac,bc}. This proves the first mixed
join. For the second, applying σ to L_01(σQ) gives R_0(Q) with ac added,
while L_11(P) is R_1(P) with ac added. Both additions contribute one edge
inside the same block, and σ fixes each block.

For DN, use the notation u<w<x<z of the DN note and put
U={u,w,x,z}. Actual flips preserve the weak partition and replace one edge
inside its fixed block. Replacing a connected local graph on U by another
with the same number of edges also preserves this information after adjoining
any common exterior. We check the five types of DN joins:

1. L_10 and L_01 have three-edge local trees on U.
2. Each target middle state and the corresponding source L_01 have
   three-edge local trees. Transfer the invariant across the target flip.
3. In a lower mixed target flip R_00(Q)↔R_01(P), U is connected at both
   endpoints, because it is connected in R_01(P) and flips preserve weak
   blocks. The identity L_00(σQ)=σR_00(Q) exchanges vertices inside one
   block. Its block data agree with those of L_01(P).
4. L_01(Q) and L_01(σQ) have the same block data: their local trees already
   connect U, and exchanging its vertices does not change how the exterior
   attaches after U is contracted.
5. L_11 and R_11 have connected four-edge local graphs, while L_01 and
   R_10 have three-edge local trees. The upper mixed target flip again
   transfers the invariant.

All vertices, including isolated ones, are retained in this argument.
The fixed strict set also makes the normal-edge count in each block invariant.

## Which components can be removed before isolation

We may use lexicographic induction on

    (number of vertices, number of natural edges, ordinary area moment).

The [DD continuation](COMPONENT_DD_PACKETS.md) proves decrease of this measure
for NN, DN, DD and corner deletion, including normalization of target envelopes.
The moment is the one in the DN completion note. Three established
combinatorial reductions are available before applying a packet equation.

- **Disconnected selected graphs.** Their weak blocks are flip invariant,
  and the component is the product of the induced components on these
  blocks. Both valuations factor. Order compression preserves ordinary
  natural diagrams and strict corners, so vertex induction applies.
- **Trees.** The fixed-envelope tree-connectivity theorem and connected
  aggregate extraction prove their component formula.
- **No mixed-acyclic state.** If reversing all strict corners creates a
  directed cycle in every state of the component, alternating corner
  deletion expresses both valuations by the same signed sum of whole
  components in strictly smaller diagrams.

See [the active-corner note](COMPONENT_ACTIVE_CORNERS.md),
[tree connectivity](COMPONENT_TREE_CONNECTIVITY.md), and
[corner differences](COMPONENT_CORNER_DIFFERENCES.md).

After these reductions, every remaining component is connected, has more
than n-1 selected edges, and contains a state acyclic after reversing the
strict corners. The NN and DN block invariants show that the first two reductions
discard whole completion classes. Inside a surviving class, only the
third reduction is needed to remove additional known components.

**Remaining isolation question.** Does each ordinary NN or DN completion
class contain at most one component left after these reductions?

If so, the packet equations give the desired individual recurrence: take the
class indicator, transport it to whole target components, and subtract the
known source components. Target diagrams decrease the displayed induction
order. The extra source components stay in the original diagram; their
identities are already supplied by the preceding reductions or the tree
theorem. The DD continuation gives an analogous sufficient condition for its
selected corner sector. The direct individual-component redistribution need
not satisfy these isolation conditions. General reconstruction, coverage by
eligible reductions, and circular recurrence transport remain unproved.

## A smaller local DN question

Two proved lifting lemmas reduce the target-middle part of DN isolation.

An exterior target flip in R_10 lifts with the same exterior endpoints to
source L_01 unless its retained long is the new strict edge ux. The selected
relations differ only by the maximal corners wz and ux. Neither can lie
inside a common natural retained-long interval, so the selected relations
inside that interval and all required cover tests agree.

An exterior target R_01(Q)↔R_01(P) flip gives an actual source
L_01(σQ)↔L_01(σP) flip. Delete the adjacent edge wx at both target endpoints,
apply the zero-stratum swap conjugacy, and then use the source 00-to-01 lift.
The deleted edge is neither exchanged nor a possible retained long.

The exceptional R_10 case is consequently the explicit pair

    Q+{ua,xz},       Q+{ax,xz},       u<a<w<x<z,

with strict uw,wz and the common strict exterior. Here Q omits ua,ax,wx,xz,
and the corresponding R_10 states must be actual target flip neighbors,
retaining ux; the target cover hypotheses are retained.
The seven-vertex example above is such a pair. A useful next lemma would
construct a source flip path under connectedness and mixed-acyclic endpoint
hypotheses. The exterior-swap comparison and paths through mixed-cyclic states
must also be controlled to prove the full isolation statement.

## Checks and provenance

The NN proof was derived by primary and independently audited by Luna in the
ordinary setting. Astra independently supplied the DN counterexample's short
certificate, audited all five block-invariance cases, and proved the two
local lifting lemmas. Primary checked these arguments.
Luna also independently audited the NN block invariant. The later DD and
direct individual-component work have separate linked notes and receipts.

Exact complete-state checks, using the previous cover-flip model, give:

| Recurrence | Vertices | Eligible saturated instances | Source components counted |
|---|---|---:|---:|
| NN | 3,4,5,6 | 1,4,15,56 | 3,24,236,3384 |
| DN | 4,5,6,7 | 1,5,21,84 | 3,27,274,3919 |

Every packet image is constant on whole target components in these tests.
The refined isolation question passes all listed instances. Source components
are counted separately for different eligible recurrence choices. The original
NN isolation condition has two collisions in the six-vertex diagram
(0,1,2,3,4,3), with strict edges {04,25} and distinguished corner 25.
The original DN condition has the seven-vertex collisions described above.
Neither unqualified condition should be used as a conjectural proof target.

External request directory:

    /lake-cache/ai-projects/requests/VerticalStripLLT/recurrence-continuation/

Receipts: `dn_scan.jsonl`, `dn_scan_seven.jsonl`, `dn_pruning.json`,
`dn_essential_scan.jsonl`, `nn_completion_result.jsonl`,
`nn_completion_six.jsonl`, and `nn_six_certificates.jsonl`;
`SHA256SUMS.json` records the script and receipt hashes. Corresponding
scripts reuse `diamond-exploration/probe.py` and the existing DN completion
graph construction. The Rust capability check was already completed for this
relation-module search; bounded Python orchestration extends those probes
without introducing a polynomial generator or a competing library. No Lean,
Rust, or LaTeX build was run. No general isolation theorem follows from these
finite checks, and the combinatorial-proof goal remains active.

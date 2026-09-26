# Termination of full forward neutral bounces

This note addresses successive uses of relation (3), rather than the search
through diagonal contacts inside one fixed diagram. It concerns strict edges
of whole diagrams. It does not concatenate coloring constraints from different
intermediate diagrams or use selected non-strict edges.

## Precise contact data

Write R_D for the strict-edge relation of a circular diagram D. A full forward
DN bounce with r >= 1 contacts has main contact vertices

    a -> p_0 -> p_1 -> ... -> p_(r-1) -> z

and parallel contact vertices

    q_0 -> q_1 -> ... -> q_(r-1),    q_i = p_i + 1 (mod n).

Every displayed arrow is strict in the source diagram. The initial DN contact
says q_0 has no incoming strict edge. The final DE contact says q_(r-1) has no
outgoing strict edge. Intermediate DD contacts supply the two parallel arrows
at each step. The target changes precisely the two endpoint arrows:

    a -> p_0, p_(r-1) -> z    become    a -> q_0, q_(r-1) -> z.

All other strict arrows remain. These are the source/target strict-edge data
of the full word relation

    U d.n V d.e W  ->  U n.d V e.d W.

The graph formulation includes every DD contact and the full exterior strict
graph. It makes no assumption that all lifted vertices lie in one period.
In the Lean interface, both source and target are valid circular diagrams;
contact data specify their strict graphs, rather than assuming polynomial
equality or a rank decrease. Normal edges are immaterial to this lemma.

## Separation and the vertex exchange

Assume the source strict graph is acyclic. Circular corner geometry gives
indegree and outdegree at most one. Both displayed paths are therefore
injective. The parallel path is a whole component: uniqueness of predecessors
and successors and its two endpoint conditions prevent any strict edge from
entering or leaving its vertex set.

If the main path met it, closure in both directions would place every main
vertex in the parallel path. This is impossible: the main path has r+2
distinct vertices, while the parallel path has r. Thus the two paths are
disjoint, including a and z.

Exchange p_i with q_i for every i and fix every exterior vertex. This is a
permutation sigma. Strict degree uniqueness classifies each source arrow as
one of the two endpoint arrows, an internal arrow of either path, or an
exterior arrow. The permutation exchanges the internal arrows in pairs,
fixes the exterior arrows, and sends the source endpoint arrows to the two
target endpoint arrows. It therefore conjugates the entire source strict
relation to the target relation. In particular, acyclicity is preserved.

## A natural-number rank

Let d_D(v) be the number of strict ancestors of v (proper reachability), and
let ell(e) in {1,...,n-1} be the natural positive circular length of an edge.
Define

    J(D) = sum_(e strict) d_D(head e) * ell(e).

For an acyclic partial injection, the depth of the head of the j-th edge in
a chain is j. Thus this is exactly the draft's sum of j times edge length,
without choosing or enumerating maximal chains.

Ancestor depth is invariant under sigma. All internal edge lengths are
preserved: both endpoints shift by +1 or both shift by -1. Exterior lengths
are unchanged. The first endpoint edge increases in length by one; the last
decreases by one. There is no modular exception: a purported first length
n-1 would identify a with q_0, contradicting separation. The existence of the
positive-length target last edge similarly excludes a zero final length.
Equivalently, the endpoint modular equations and the positive < n bounds
prove the two length identities directly.

Write e_in and e_out for the source endpoint edges. Reindexing the target
edge sum by sigma gives the exact identity

    J(D') + d_D(z) = J(D) + d_D(p_0).

The source has a nonempty strict path from p_0 to z. In an acyclic graph,
proper ancestor sets grow strictly along a nonempty path: all ancestors of
p_0 remain ancestors of z, and p_0 itself is a new ancestor. Hence

    d_D(p_0) < d_D(z),    so    J(D') < J(D).

In the partial-injection case the difference is exactly r, agreeing with
the draft's full-bounce calculation. Strict decrease alone suffices below.

## The contradiction and vanishing

Suppose D_0,D_1,... is an infinite sequence of full forward neutral bounces.
If the strict graph of D_0 were acyclic, the conjugacies would preserve
acyclicity and J(D_0)>J(D_1)>... would be an infinite decreasing sequence of
natural numbers. This is impossible. Thus the strict graph of D_0 contains
a directed cycle.

Every coloring counted by its LLT polynomial must increase strictly along
that cycle. Transitivity would give c(v)<c(v), so there are no admissible
colorings. The whole coloring LLT polynomial is zero for every finite
alphabet. This final vanishing fact was already formalized in
`Circular/StrictCycleVanishing.lean`.

This is termination for successive forward neutral moves. It does not assert
that an arbitrary finite return of a marker residue forces zero, and it does
not prove the circular coloring or HRV bounce identities themselves. Those
identities, plus existence of a terminal or area-decreasing move, are separate
steps toward the full expansion. Geometric area counts strict corners as
half-squares; the actual DN word rewrite preserves it. The strict-contact
interface alone does not assert this, because it leaves normal edges unconstrained.

## Lean declarations and scope

`Circular/NeutralContacts.lean` defines `FullNeutralBounce D D'` for arbitrary
circular size and arbitrary contact count. Its fields are the two paths,
their strict arrows, the next-residue equations, the two free endpoints,
and the exact replacement of the endpoint arrows. Separation, graph
conjugacy, and rank decrease are conclusions, not fields.

`Circular/NeutralTermination.lean` proves:

- `FullNeutralBounce.preserves_acyclic`;
- `FullNeutralBounce.strictRank_lt`;
- `strict_cycle_of_infinite_full_neutral_bounce`;
- `coloringLLT_eq_zero_of_infinite_full_neutral_bounce`.

The last theorem quantifies over every finite alphabet and uses the independent
coloring sum. There are no recurrence or vanishing assumptions. The complete
reverse search and its contact extraction are now proved in `BounceSearch`,
`ReverseBounceContacts`, and `DNRealization`. `GeometricArea` proves the actual
DN successor preserves half-square area and decreases strict rank. No separate
word decoder is required by this direct periodic-boundary implementation.

Direct coloring and HRV NN/DN identities are also proved. Their generalized
DD propagation and ND branches remain in [the active goals](../CIRCULAR_GOALS.md).

# Reduction when the ND terminal and root share an edge orbit

This note explains the completed uniform reduction. The full actual polynomial
identities are locally checked as `Diagram.exists_nd_alias_reduction` in
[AliasRecurrences.lean](../../VerticalStripLLT/Circular/AliasRecurrences.lean).
`Diagram.expansion_of_nd_alias` gives the area-induction step, including
preservation of strict acyclicity. Independent Astra review audited the
Aristotle candidate before primary integration.

Let the successive lower contact vertices be p_0,...,p_(r-1), and put
q_j=p_j+1 on the integer cover. The root z has residue q_0 and strict tail
p_(r-1). Its strict length is L. The initial ND boundary has
b(p_0)=b(q_0). Write z=q_0+kn; then b(p_0)=p_(r-1)-kn.

The main and parallel contact paths concatenate into the strict path

```
p_0 → ... → p_(r-1) → q_0 → ... → q_(r-1).
```

Acyclicity makes all 2r projected vertices distinct. Therefore the simultaneous
adjacent swaps p_j ↔ q_j are disjoint. The strict path is a whole component:
p_0 has no incoming strict edge (ND), and q_(r-1) has no outgoing strict edge
(the root's DE boundary gap). The case L=2 would identify q_(r-1) with p_0, contradicting the
free endpoint and the first outgoing edge of the main path. Thus L≥3; this
length bound does not require an additional acyclicity hypothesis.

## Valid successor

Decrease the area at p_0 by one and at q_0 by two. Replace the root strict edge
p_(r-1) → q_0 by q_(r-1) → p_0, of natural length L−2. Keep every other strict
edge. Both new row areas equal L−2. The original DE gap and the equality of the
initial ND boundaries prove cyclic area validity and the new strict-corner
condition. The strict count is unchanged; doubled geometric area decreases six.

Related Lean: `../../VerticalStripLLT/Circular/AliasArea.lean` and
`AliasTarget.lean`. `Diagram.aliasTarget_doubledArea` proves the decrease.
`Diagram.exists_aliasTarget_of_reverseBounce` in `AliasRealization.lean` derives
the constructor inputs and decrease directly from the actual search.
The constructor has no polynomial identity assumption.

## Forced edge sets

Let N be the source normal edge set and define, using natural circular lengths,

```
B = {p_j → q_j : 0≤j<r}
C = {q_(j−1) → p_j : 1≤j<r}
H = {p_last → p_0, q_last → p_0, q_last → q_0}.
```

These are disjoint normal-edge sets. Target normals are exactly N minus H.
The source strict chain forces B to ascend and C∪H to descend. The target
strict chain, q_0→...→q_last→p_0→...→p_last, forces C to ascend and B to descend.
All nonlocal strict edges are fixed by the paired swaps.

Removing a forced ascent contributes q to the coloring polynomial, and q+1 to
the shifted HRV expression. A forced descent contributes no factor: selecting
it creates a cycle, and it is never a coloring ascent. The checked
`ForcedColoring`, `ForcedOrientation`, and `ForcedReduction` modules establish
these facts for arbitrary edges forced by strict reachability, with the original
HRV semantics. Restricted sums are not silently identified with valid diagrams.

## Common normal relation

After deleting B∪C∪H from N, both heads p_j and q_j have the identical incoming
lift interval [ell_j+2,p_j), where ell_j=p_(j−1) for j>0 and
ell_0=b(p_0). Its endpoints lie just after and just before complete swapped
pairs, so the interval is invariant under the paired swaps.

For an exterior head v, boundary monotonicity and the strict corners show that
b(v)=q_j+hn can occur only at v=q_(j+1)+hn when j<r−1. The final boundary value
q_last+hn never occurs, by the root DE gap. Thus an exterior head's incoming
interval cannot cut a swapped pair. Its strict incidences are fixed, since the
contact vertices form a whole strict component. This proves full periodic
invariance of the remaining normal relation.

The paired integer swap conjugates the strict relations of source and target.
Every p_j has a strict outgoing edge, so a pair never contains two source sinks.
The swap preserves order on sinks, including when paths wind. Actual lifted-HRV
conjugacy therefore matches the common monomials.

The source has r forced ascent factors and the target r−1. Finite-subset
factorization and cancellation give the proved identities

```
coloringLLT D m = C(q) * coloringLLT Q m
shiftedOrientationExpansion D = C(q+1) * shiftedOrientationExpansion Q.
```

The geometric half-square area drops by three (doubled area by six).
`AliasReductionContacts` constructs the contact data; `AliasReductionRelations`
proves strict/exterior lifted conjugacy; `AliasReductionForced` proves the
coloring identity; `AliasReductionOrient` transports the actual HRV fibers.
The common factor after shifting q is q+1, so the actual semantic bridge
transfers directly from the smaller target.

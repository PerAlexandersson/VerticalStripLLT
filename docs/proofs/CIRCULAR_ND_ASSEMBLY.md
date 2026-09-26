# Circular ND assembly: separated branch and interior overlap

This note separates the completed disjoint reduction from the remaining interior
obligation. Direct ND and full NN elimination were checked at `1d5005d`; see
[CIRCULAR_DIRECT_ND.md](CIRCULAR_DIRECT_ND.md) and
[CIRCULAR_DD_PROPAGATION.md](CIRCULAR_DD_PROPAGATION.md).
The author's intended route uses one-bounce identities and local elimination.
An unrestricted projected general R4 identity is not assumed.

## Completed disjoint terminal branch

`Diagram.exists_nd_separated_reduction` proves the actual coloring and HRV
identities for `ReverseBounceN D t x k` under precisely

```lean
∀ i ≤ k, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)
```

The six `NDSeparated` modules construct every intermediate diagram, transport
the counted searches and identify the two targets, with doubled-area drops
two/four. `NDSeparatedContacts` derives main/parallel separation from this
hypothesis and source acyclicity; it assumes no common no-wrap interval.

As in direct ND, N=unstrict g, E=delete g, S=lowerStrict g, and
J=delete the newly exposed lower corner from E. Full NN applies to N and J.
The lowered S can be cyclic. `NDSeparatedHyp.dS_admissible_iff` proves that S
and the root-shortened Q are acyclic together by paired-chain conjugacy. The
external endpoints may coincide; their distinctness is not assumed. Thus full
DN applies when S is acyclic, and both actual expressions vanish when S is
cyclic. Four R1 identities, full NN twice and this DN identity give the seven
relations needed by the checked cancellation lemma.

`Diagram.expansion_of_nd_separated` supplies the area-induction step.
`separatedNDInductionStep` discharges the separated input of the outer assembly,
and `Diagram.expansion_of_interior_nd_step` retains only the interior input.

## Interior terminal overlap

`DDLocalData.exists_oneBounce_restart_of_interior_overlap` produces a zero-DD
NN/DN restart in the resolved child R. Here R has doubled area D+1. A direct NN
move exits to area D−1; subsequent direct ND would likewise exit below D.
A direct DN move preserves the auxiliary area, so its semantic equality alone
does not justify applying outer area induction to its target.

The next geometric task is to track the restart through direct DN moves until
an exit with a valid outer measure is reached. The missing strict head moves
by the offset between the two overlapping chains, not necessarily by one
contact. A proposed fixed `i−1` consecutive-slide count is therefore not yet a
proved invariant. A boundary case can expose a nonstrict corner. For such an
R1 exit, deletion lies below D, while strictification has area exactly D and
requires a strict-rank comparison with the original source (or a separate
cancellation argument). Such a comparison is not automatic: the exposed-corner
strictification is not uniformly a rank-decreasing neutral transport of D.
Likewise, a rotation exit with accumulated coefficient one does not isolate
the original semantic difference by cancellation. The existing mixed DD/neutral termination theorem
supplies neither this exit classification nor that comparison.

The root-alias branch is already complete through `expansion_of_nd_alias`.
The checked outer induction already assembles direct ND, root alias, disjoint
ND, strict-cycle vanishing and the other branches. The interior exit remains
its sole unproved input.

## A proved additional exit

`Diagram.coloringLLT_shifted_eq_expansion_of_normal_comparable` now proves the
full semantic bridge whenever each normal edge has endpoints comparable by
strict reachability, in either direction. It does not require strict acyclicity
as an input. The proof inducts on selected normal subsets: a forward strict
path makes the extra coloring constraint and HRV edge redundant; a backward
strict path makes that selected term cyclic and zero. The empty selected set
uses the previously proved strict-chain expansion. Summing the independently
matched selected-set terms gives the full coloring–HRV equality.

`Diagram.coloringLLT_shifted_eq_expansion_of_strict_total` covers a strict chain
through all vertices. This base can close some overlap configurations without
finding a smaller diagram. It does not by itself handle remaining interactions
between distinct strict components. The general interior exit classification
remains open.

## A proved two-corner exit

`Diagram.expansion_of_two_nonstrict_corners` closes any auxiliary diagram T
with doubled area at most a+1 and two distinct nonstrict corners, assuming the
semantic bridge below area a. Strictify the first corner to obtain S, then
resolve the second corner in S. The three leaves have doubled areas
T−2, T−3 and T−2, respectively. Both models satisfy the same two R1 identities,
so the bridge for the leaves proves the bridge for T. The DD wrapper is
`DDLocalData.expansion_of_resolved_two_corners`.

This supplies an additional exit without a rank comparison. The restart
geometry does not yet guarantee two missing corners: proving that a sequence
exposes a second corner while retaining the first remains a separate task.
Changing the root alone does not remove every interior case, because eligible
roots require genuine area descents and a source can have only one such root.

## Further measure audit (not a proved exit)

Putting strict-component sizes before strict rank does not remove the known
rank-increase issue. The relevant DD resolution splits a component of size L
into L−1 and a singleton; neutral moves preserve component sizes. An eventual
strictification that rejoins the singleton restores the original partition,
even when strict rank increases. Rejoining a different singleton can also
preserve the partition without giving a literal rotation. Thus a partition
refinement alone does not close the unresolved branch.

Joining the surviving chain to a different chain of size K≥2 would instead
replace (L,K) by (L+K−1,1), increasing the sum of squared sizes by
2(L−1)(K−1). This suggests an additional measure for that subcase, but both
the incidence classification and the partition-preserving remainder still
need proofs. No Lean theorem assumes this proposed classification.

# Remaining ND assembly after direct ND and NN elimination

This note records unproved obligations. Direct ND and full NN elimination are
locally checked at `1d5005d`; their explanations are in
[CIRCULAR_DIRECT_ND.md](CIRCULAR_DIRECT_ND.md) and
[CIRCULAR_DD_PROPAGATION.md](CIRCULAR_DD_PROPAGATION.md).
The author's intended route uses one-bounce identities and local elimination.
An unrestricted projected general R4 identity is not assumed.

## Disjoint terminal branch

For `ReverseBounceN D t x k`, the terminal is `x = boundary^[k+1] t`.
The relevant separation condition excludes the terminal upper vertex from
all strict main heads, including the original root:

```lean
∀ i ≤ k, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)
```

Strict incoming-edge uniqueness should propagate this condition to separation
of the complete main and parallel contact paths. This is a geometry obligation,
not an additional hypothesis for the final circular theorem.

Let g be the terminal strict edge. As in direct ND, put N=unstrict g,
E=delete g, S=lowerStrict g, and J=delete the lowered corner from E. The needed
transport theorem retains the same DD count and root eligibility, with NN
terminal type in N and J and DN terminal type in S. Root shortening must commute
with these corner changes. Then four R1 identities, full NN twice and full DN
once give the same seven-equation cancellation as direct ND, with final area
drops two/four.

Lowering g can create a strict cycle even when D is acyclic. In that case the
corresponding root-shortened diagram Q must also be shown cyclic, so both terms
in the needed DN identity vanish. One route is strict-path splicing; another uses the checked theorem
`neutralExchange_acyclic_iff`, supplied with explicit separated inner paths
rather than an acyclicity assumption on S. Endpoints of that
exchange may coincide. Do not infer that S is acyclic from the source D alone.

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
These cases must be assembled with the disjoint branch, strict-cycle vanishing,
and the half-square-area/strict-rank induction. None of the obligations above
has yet been exported as a Lean theorem.

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

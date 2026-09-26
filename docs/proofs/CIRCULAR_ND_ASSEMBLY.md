# Circular ND assembly: separated branch and interior overlap

This note separates the completed disjoint reduction from the remaining interior
obligation. Direct ND and full NN elimination were checked at `1d5005d`; see
[CIRCULAR_DIRECT_ND.md](CIRCULAR_DIRECT_ND.md) and
[CIRCULAR_DD_PROPAGATION.md](CIRCULAR_DD_PROPAGATION.md).
The author's intended route uses one-bounce identities and local elimination.
An unrestricted projected general R4 identity is not assumed.

## Strict loops versus shared contacts

The author's strict-loop argument is already checked. In a fixed diagram,
`ReverseBounce.selected_path` follows actual strict edges. A repeated vertex
on that directed walk forces a strict cycle, so both actual models vanish.
`exists_complete_reverseBounce` uses strict ancestor depth to terminate the
search in the acyclic case. `coloringLLT_eq_zero_of_infinite_full_neutral_bounce`
also proves vanishing for indefinite sequences of the specified neutral moves.

The remaining interior identification is between two offset contact tracks:
the upper terminal vertex x+1 lies inside the main chain starting at x.
It supplies a path from x to x+1, not a return to x. Both tracks may therefore
lie inside one acyclic strict component. The checked interior restart already
reduces this situation to a single NN or DN bounce. The outstanding work is
the area accounting for the resulting auxiliary diagrams, as detailed below.
No independent multibounce identity is needed as an assumption.

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

`Diagram.expansion_of_nd_interior_overlap_first_contact` now closes the case
where x+1 aliases the first contact b(t). The explicit-index restart theorem
`DDLocalData.oneBounce_restart_of_interior_overlap_at` identifies the new
terminal as x itself in this case, so its lower row remains nonstrict and
the restart is NN. The NN-shortened child and DD-deletion child both have
doubled area D−1. This proof uses only lower-area induction, without saturation
or strict rank. Deeper interior contacts remain open.

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

The uniform strict-corner adjacency lemma is also checked in
`StrictCornerAdjacency.lean`. For a strict edge a→b and a third vertex v,
the normal edge a→v exists exactly when v→b does. The proof uses maximal
outgoing length at a strict corner and monotonicity of the lifted boundary;
it needs neither acyclicity nor a common no-wrap interval. It is now used in
the proved chain-plus-isolated-vertex base described below. A general exit
from every interior diagram remains open.

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

## Extended-termination review

A read-only Sonnet consultation proposed tracking the semantic defect through
DD, neutral and single-corner strictification steps. The algebra is valid:
if every deletion side is below the original area and hence has zero defect,
then q times the source defect equals q times the final strictified defect.
Cancellation transfers the defect without comparing ranks. This is already
implicit in the coefficient-one issue above and supplies no new geometric exit.

The proposed unrestricted no-repeat theorem for this enlarged relation fails:
the previously audited rotation route can be repeated equivariantly until the
finite-order rotation returns to the original acyclic diagram. That witness
is covered by the comparable-endpoint base, so a strategy forced to stop at
such bases might avoid it; the strategy and termination invariant would still
require proofs. Arbitrary additional DD steps can also raise the auxiliary
area enough that a deletion side is no longer below the original area. The
side-term condition cannot be omitted. Primary and independent Astra review
rejected the unrestricted termination proposal; no such Lean assumption or
theorem was added.

## Why rotation alone does not give an exit

A further independent audit identifies a conserved quantity. Write
Δ_D = xQShift(LLT_D) − evalElementary(HRV_D), and s_D = |D.strict|.
Assume the deletion-side defects vanish by a valid induction hypothesis.
The following relations then preserve q^(s_D) Δ_D:

- DD gives q Δ_D = Δ_R and s_R = s_D−1.
- Actual neutral DN preserves both the defect and strict count.
- R1 strictification gives Δ_T = q Δ_S and s_S = s_T+1.

Consequently, any excursion using only these moves and ending at a rotation
returns with coefficient one. Rotation invariance would make the resulting
equation an identity, not a proof of vanishing. Rotation can close an excursion
only when it identifies the endpoint with an independently solved diagram,
or as part of a larger relation system with a nonzero annihilating coefficient.
The remote finite experiments supplied no uniform certificate of the latter.
This is an audited algebraic limitation, not an additional Lean assumption.
There is no justification for building rotation machinery solely to solve the
coefficient-one exit.

## Audit of a terminal auxiliary shape

Suppose an acyclic auxiliary diagram has exactly one nonstrict corner, at
row p, and no `EligibleDE` seed. If all row areas are positive, every strict
area descent must occur at p: a descent starts at area at least two, and a
strict corner at that row would be an eligible seed.

For constant positive area, there are n corners and n−1 strict edges. The
acyclic strict partial-injection graph is therefore one spanning chain, so
the existing strict-total base applies.

For nonconstant positive area, cut the cyclic listing immediately after p.
The areas increase weakly, with increments zero or one, up to the unique drop.
Writing d=max(area)−min(area)>0, there are d rises and n−d−1 plateaus. Every
plateau corner is strict, so the strict graph has n−d−1 edges and d+1 components.
Positive areas supply every cyclic adjacent natural edge. If every normal edge
had strict-comparable endpoints, these adjacent edges would force a single
strict component, contradicting d+1>1.

Thus the two terminal hypotheses alone do not put the diagram into the
comparable-endpoint base. The chain-plus-singleton base could apply only for
d=1 and component sizes (n−1,1); even d=1 can require a more general two-chain
argument. This is a mathematical classification audit, not yet a Lean theorem
or a proved description of all configurations reached by the interior route.
In particular, no claim that the completed chain-singleton base closes all
deeper interior cases is justified.

## Zero-area cuts do not provide a new auxiliary exit

The zero-cut geometry is checked in `ZeroCutGeometry.lean`: if row c has
area zero, every selected lifted edge and walk starting in [c,c+n) remains
there. The actual lifted HRV therefore also lies in that interval. The proof
uses boundary(c+n)=c+n and boundary monotonicity; it does not assume acyclicity
for the edge or walk statements.

Transporting the ordinary expansion through this cut would additionally need
a Schröder-word decoder and edge correspondence, an orientation equivalence,
and comparison of ordinary finite HRV with circular lifted HRV. The repository
has no such decoder. The interval lemma is not itself the ordinary semantic
bridge, and no full conversion has been started.

More importantly, `ZeroRowsTransport.lean` proves that the concrete DD and DN
moves preserve zero-area rows pointwise: they raise a positive row and lower
a row of area at least two.
Thus they cannot turn a positive-area interior source into a diagram with a
zero-area cut. Bare `FullNeutralBounce` and `NeutralTransport` only constrain
strict graph data, so this geometric claim must use the actual constructors.
An ordinary-cut base would not close the remaining positive-area auxiliary
case by these moves alone.

## Finer terminal restrictions (mathematical audit)

For the positive terminal family above, write H=area(p), m=area(p+1) and
d=H−m. The strict sinks occupy the consecutive residue block
res(p−H),...,res(p−m). Indeed, away from the unique missing corner, the lifted
boundary increments by zero or one. Its unit increments correspond to strict
plateaus, whose tails exhaust [p+1−m,p+n−H−1]. The complement is the stated
sink block of size d+1.

The initial interior DD resolution also produces an isolated strict vertex:
the deleted parallel edge ends at a strict sink, and its deletion isolates that
sink before the conjugacy. Neutral strict-graph conjugacies preserve a singleton
component. These restrictions still do not force the remaining components to
form one chain. A general chain-shuffle calculation needs the normal-edge
incidences between different chains; component sizes alone do not determine
either actual model. This paragraph records audited mathematics, not additional
Lean declarations or a proved general exit.

## Saturation does not force the chain-singleton base

The restriction also fails for the original saturated source, not merely for
an auxiliary terminal diagram. The following obstruction to that proposed
classification occurs in the completed interior request's report and checks
directly by hand:

```
n = 8
area = (3,4,4,4,3,4,5,5)
strict heads = {1,2,3,6,7} (exactly all corners)
strict chain = 5 -> 1 -> 6 -> 2 -> 7 -> 3
isolated strict vertices = 0, 4
```

The eligible root t=7 has boundary iterates
7 -> 2 -> -2 -> -7 -> -11. Its root east gap is 2. The first three contacts
are DD with east gap zero; x=-11 is ND, since its residue 5 is nonstrict
while x+1 has strict residue 6. That residue equals the second contact -2,
so this is a deeper interior overlap. The strict graph is acyclic, yet has
three components. In particular, neither strict-totality nor
`ChainSingletonData` follows from saturation and interior overlap. The normal
edge 0 -> 1 also joins different strict components.

Even allowing any number of isolated vertices does not give a source
classification. Changing only area(0) from 3 to 4 adds the strict corner
4 -> 0. The resulting saturated source has two nontrivial strict chains of
sizes 6 and 2, with no isolated vertices. The same contact iterates and i=2
overlap remain valid; the eligible root's gap decreases from 2 to 1. Thus a
general interior argument must also handle interactions between nontrivial
strict components. This strengthened witness was independently checked by
the primary and read-only Astra reviewer without new computation or builds.

This refutes only those proposed classifications, not the desired HRV formula.
It justifies retaining a general interior exit obligation after the completed
chain-singleton semantic proof. No additional example module or computation
was introduced; this is a proof-strategy counterexample, not a new theorem
milestone.

## Completed chain-singleton semantic base

`ChainSingletonData.coloringLLT_shifted_eq_expansion` now proves the actual
bridge for a strict chain c_1,...,c_L and one isolated strict vertex v, with
arbitrary finite alphabet and L≥1. No no-wrap or bounce assumption is used.
For a_j=[c_j→v normal], b_j=[v→c_j normal], corner geometry gives
a_j=b_(j+1). Put I=#forward internal normals, M=sum_(j<L) a_j,
A=I+M and r=M+b_1+a_L. Both evaluated expressions are proved equal to
(1+q)^A * (e_1*e_L + r*q*e_(L+1)).

On the coloring side, the isolated color occupies at most one strict insertion
gap; the checked insertion sums give the displayed formula. On the HRV side,
internal forward normals factor as (1+q)^I, while internal backward selected
normals force a cycle. External outgoing/incoming position sets U,V are acyclic
exactly when every j in U is smaller than every h in V. A selected incoming
edge or an outgoing edge at the last chain vertex gives one sink and one fiber.
Otherwise strict continuation dominates each external edge in the actual
integer lift, so the HRV monomial remains e_1*e_L. Grouping nonempty V by its
least member completes the finite selection sum.

The six `ChainSingletonSelection`, `Subsets`, `Insertion`, `Orientations`,
`Reduction`, `Expansion` modules separate these arguments (each filename
has the `ChainSingleton` prefix). The local build and axiom inventory passed;
this section records a completed semantic base, not a proposed recurrence.

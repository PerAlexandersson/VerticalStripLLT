# Remaining circular proof obligations

The full theorem is still open:

```lean
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion
    {n : ℕ} (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)
```

This is a target, not an exported declaration. Both sides are independently
defined. The eventual theorem must have no recurrence or semantic assumptions,
and must include every finite alphabet, including the empty alphabet.
[Verified results](CIRCULAR_STATUS.md) and [current ownership](../HANDOFF.md)
are recorded separately.

## Complete the reduction to one-bounce relations

The user clarified the intended route: use the ordinary local elimination
argument to reach one-bounce configurations. A genuine directed strict loop
has zero polynomial, handled by the existing vanishing theorems. Counts and
contact lists are auxiliary bookkeeping; a projected multi-bounce R4 identity
is not a prerequisite and must not be assumed.

The actual q-weighted DD resolution is proved for both models. Both smaller
search children for NN/DN are supplied by the deletion and resolved-child
lemmas. NN elimination and its final cancellation are now complete through
`Diagram.expansion_of_nn`. The corresponding DN closing triple and elimination are now complete through
`Diagram.exists_dn_reduction` and `Diagram.expansion_of_dn`. Assemble the
remaining ND search configurations.
`LocalEliminationStep.measure_lt` already proves termination of mixed concrete
DD/neutral segments by `(strict.card, strictRank)`; it does not include R1
strictification or prove that a suitable next move always exists.
Some auxiliary diagrams temporarily have larger half-square area. Both sides of the concrete NN closing triple and its cancellation are proved.
The DN analogue also uses auxiliary contact-count induction; it never invokes
outer area induction at a larger diagram.

The [interior-overlap analysis](proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md) explains
why applying full R4 immediately is invalid, and why this does not invalidate
the intended one-bounce route. In the displayed witnesses DD elimination
creates an earlier restart, followed by direct NN. The uniform interior
restart is now proved by `DDLocalData.exists_oneBounce_restart_of_interior_overlap`.
Account explicitly for neutral moves at an auxiliary
area level before invoking the outer induction.

The root-overlap branch is independently complete through
`Diagram.expansion_of_nd_alias`. The direct one-bounce ND branch is also complete through
`Diagram.expansion_of_oneBounce_nd`, with doubled-area drops two and four and
no acyclicity assumption. Its [proof explanation](proofs/CIRCULAR_DIRECT_ND.md)
records the seven local identities. The separated-contact branch is now proved
by `exists_nd_separated_reduction` and `expansion_of_nd_separated`, including
simultaneous vanishing of cyclic intermediates. The remaining ND work is the
interior-restart exit, including its auxiliary-area accounting. The
[ND assembly](proofs/CIRCULAR_ND_ASSEMBLY.md) records the completed disjoint
transport and the remaining interior obligation.
See [DD local elimination](proofs/CIRCULAR_DD_PROPAGATION.md) for the checked
identities and the earlier algebraic propagation route.

## Final induction and corollaries

The outer induction on `(doubledArea, strictRank)` is checked in
`Diagram.expansion_of_nd_induction_step`. Corner reduction handles nonsaturated
sources; strict cycles and no-normal-edge diagrams supply bases; complete
reverse search covers NN, DN and ND. R1 and NN decrease area, and full DN
preserves area while decreasing strict rank.

`Diagram.expansion_of_interior_nd_step` now has exactly one open input:
`InteriorNDInductionStep`. The separated input of the earlier assembly is
discharged by `separatedNDInductionStep`; direct ND and root alias are discharged
internally. Prove the interior input to instantiate the checked induction.
This conditional declaration does not assert the full theorem and does not
replace either independently defined polynomial by a recursive object.

After the semantic bridge, transfer the independently proved HRV coefficient
positivity and degree to the coloring polynomial. The last-variable
alphabet-specialization interface is already proved directly from coloring
semantics. The neutral-termination lemma, selected
subset expansion, HRV construction, and direct recurrences are completed
results, not new work items.

Complete flip-component expansions and omega translation remain downstream;
see [the retained component interfaces](CIRCULAR_FLIPS.md). They are not
prerequisites for the aggregate circular theorem. No new examples or general
symmetric-functions library are planned.

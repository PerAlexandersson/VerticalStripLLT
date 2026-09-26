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
`Diagram.expansion_of_nn`. Complete the corresponding DN closing triple and
elimination, then assemble the remaining ND search configurations.
`LocalEliminationStep.measure_lt` already proves termination of mixed concrete
DD/neutral segments by `(strict.card, strictRank)`; it does not include R1
strictification or prove that a suitable next move always exists.
Some auxiliary diagrams temporarily have larger half-square area. Both sides of the concrete NN closing triple and its cancellation are proved.
The DN analogue remains an auxiliary contact-count induction, not an invocation
of outer area induction at a larger diagram.

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
records the seven local identities. The remaining ND work is elimination and
restart assembly for a longer search, including its auxiliary-area accounting.
See [DD local elimination](proofs/CIRCULAR_DD_PROPAGATION.md) for the checked
identities and the earlier algebraic propagation route.

## Final induction and corollaries

Use lexicographic induction on `(doubledArea, strictRank)`. Strict cycles and
no-normal-edge diagrams already have their semantic base theorems. R1 and NN
strictly decrease area; the complete DN target preserves area and decreases
strict rank. Supply the local elimination and remaining ND recurrences and use the
proved complete reverse search to exhaust all cases.

After the semantic bridge, transfer the independently proved HRV coefficient
positivity and degree to the coloring polynomial, and add the circular
alphabet-specialization interface. The neutral-termination lemma, selected
subset expansion, HRV construction, and direct recurrences are completed
results, not new work items.

Complete flip-component expansions and omega translation remain downstream;
see [the retained component interfaces](CIRCULAR_FLIPS.md). They are not
prerequisites for the aggregate circular theorem. No new examples or general
symmetric-functions library are planned.

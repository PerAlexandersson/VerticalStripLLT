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
lemmas (current local checks are in HANDOFF). Finish the geometric elimination
and its well-foundedness/area accounting, then apply the direct local identities.
Some auxiliary diagrams temporarily have larger half-square area.

The [interior-overlap analysis](proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md) explains
why applying full R4 immediately is invalid, and why this does not invalidate
the intended one-bounce route. In the displayed witnesses DD elimination
creates an earlier restart, followed by direct NN. Uniformly an interior
collision should restart at a one-bounce NN or DN contact; prove this from
actual search geometry. Account explicitly for neutral moves at an auxiliary
area level before invoking the outer induction.

The root-overlap branch is independently complete through
`Diagram.expansion_of_nd_alias`. Genuinely local ND relations still need their
actual diagram transformations and two-model identities where used.
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

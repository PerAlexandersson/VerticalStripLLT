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

## DD propagation

Direct NN and DN are proved for both models. Extend them through any number
of DD contacts by induction on `ReverseBounceN`'s contact count, quantifying
over the intermediate diagrams. Some intermediates have larger area.

The first DD elimination and the deletion child's counted transport,
eligibility, terminal flags, and acyclicity have been checked locally.
The remaining work is the raised child's corresponding transport, the final
corner-triple identifications, and assembly of the generalized recurrences.
See [the exact DD argument](proofs/CIRCULAR_DD_PROPAGATION.md).

## Remaining ND branches

The overlapping ND branch is complete: `Diagram.expansion_of_nd_alias`
supplies its actual area-induction step, including target acyclicity.

Root nonalias does not imply disjoint contacts. An independently audited
[interior-overlap obstruction](proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md) makes both
naive R4 targets cyclic, although the source is acyclic and saturated.

For genuinely disjoint contacts, construct the R4/positive-R8 targets and
prove the intermediate contact transports, actual two-model identities, and
area decreases. Interior overlap requires a separate reduction or a uniform
semantic theorem covering that family. Do not attempt to prove its false
exclusion from acyclicity or from root nonalias.

## Final induction and corollaries

Use lexicographic induction on `(doubledArea, strictRank)`. Strict cycles and
no-normal-edge diagrams already have their semantic base theorems. R1 and NN
strictly decrease area; the complete DN target preserves area and decreases
strict rank. Supply the remaining generalized/ND recurrences and use the
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

# Remaining circular proof obligations

The full theorem remains unproved:

```lean
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion
    {n : ℕ} (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)
```

This is a target, not an exported declaration. Both polynomial models are
independently defined. The result must include every finite alphabet, including
the empty alphabet, without recurrence or semantic assumptions.

## Interior column-reversal reduction

The active route is [column reversal](proofs/CIRCULAR_COLUMN_REVERSAL.md).
The merged strict component, finite reversal, actual valid smaller target,
doubled-area decrease, periodic integer reversal and exact strict lifted
transport are proved. They are not remaining implementation tasks.

The target-specific obligations are:

1. Prove that an outside head's boundary cannot lie inside a moved column.
   Its incoming interval therefore contains a whole column or none of it.
2. Prove order preservation between distinct lifted columns and fixed outside
   points. Together with periodicity, this preserves the bounds 0<length<n
   for exterior edges. Distinct columns may be adjacent.
3. Prove exterior normal-edge and lifted-edge correspondence. Strict component
   heads already have the exact transported boundary; the old nonstrict source
   needs its separate threshold formula. Outside heads keep their boundaries.
4. Prove order preservation for all selected integer sinks. Finite graph
   conjugacy alone does not identify the actual HRV fibers.
5. Remove internal normal edges with the existing forced/descent APIs,
   transport the residual coloring and orientation sums, and use the smaller
   target's induction hypothesis. Cancel its nonzero forced-edge factor;
   no comparison of source and target forced-edge counts is needed.

These results must discharge `InteriorNDInductionStep` with its existing
hypotheses. The conditional theorem `Diagram.expansion_of_interior_nd_step`
then supplies the outer induction. No stronger geometric assumption may be
added to the final circular theorem.

The earlier paired-child route and failed shortcuts remain documented in
[ND assembly](proofs/CIRCULAR_ND_ASSEMBLY.md). The ordinary raised child uses
shorter-prefix induction, not smaller area. Strict-loop vanishing does not
identify offset-track intersections with cycles, and arbitrary rewrite
termination is not a required theorem. The completed chain/singleton base
does not classify every interior source.

## Final corollaries

After proving the actual coloring–HRV equality, transfer the independently
proved HRV coefficient positivity and weighted degree to the coloring model.
Alphabet specialization is already proved directly from coloring semantics.

[Verified results](CIRCULAR_STATUS.md) and [current ownership](../HANDOFF.md)
are recorded separately. Complete flip-component expansions and omega
translation remain downstream; see [retained interfaces](CIRCULAR_FLIPS.md).
No new examples or general symmetric-functions library are planned.

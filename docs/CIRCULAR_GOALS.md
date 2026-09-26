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
doubled-area decrease, periodic integer reversal, strict/exterior edge transport,
sink order and actual residual coloring/HRV equality are proved. They are not
remaining implementation tasks.

The remaining reduction steps are:

1. Partition the internal normal edges by the order along the strict component
   chain. For D this is `K.vertexEmbedding`; for Q it is that embedding followed
   by `K.reversalPerm`. Forward internal edges are forced ascents and backward
   internal edges are forced descents.
2. Apply the existing forced/descent set APIs to both actual polynomial models.
   Identify the remaining normal pairs with `Diagram.exteriorNormalPairs`,
   whose coloring and HRV transport are now proved. Within each diagram, the
   two models must use the same forced-edge count.
3. Apply the smaller target's induction hypothesis and cancel its nonzero
   coefficient factor. Restore the source factor. No comparison between the
   source and target forced-edge counts is needed.

These steps must discharge `InteriorNDInductionStep` with its existing
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

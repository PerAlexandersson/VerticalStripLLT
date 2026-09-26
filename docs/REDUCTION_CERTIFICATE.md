# The sufficient recurrence certificate and its boundary

The ordinary expansion is proved using `SatisfiesReductionRecursion`.
The original manuscript-facing `SatisfiesRecursion` remains unchanged; generic
uniqueness from those narrower clauses is a separate open claim.
[The audit](RESTRICTED_BOUNCE_AUDIT.md) explains the exact missing implication.

`SatisfiesReductionRecursion q e F` extends the restricted clauses by the NN
and DN identities with middle word `east :: V`, where V has no east steps,
and the same valid-word, return, and strict-gap conditions. The second extra
clause is needed by DD propagation. The manuscript's unrestricted concrete
orientation statements permit these instances; the restricted generic
recurrence alone does not currently supply them.

The following are all proved:

- `coloringLLT_satisfiesReductionRecursion` and
  `orientationExpansion_satisfiesReductionRecursion`, independently from the
  combinatorial definitions;
- `SatisfiesReductionRecursion.thirdBounce` and all three generalized bounce
  reductions, including valid targets and required measure decreases;
- `SatisfiesReductionRecursion.map`, transporting identities without claiming
  that an arbitrary ring homomorphism preserves nonzeroness;
- `SatisfiesReductionRecursion.unique`, using size, east count, and first-east
  height;
- `coloringLLT_eq_eval_orientationExpansion`, with no recurrence or uniqueness
  assumption in its statement.

The polynomial domains provide nonzero-factor cancellation where the source
uses division by q−1. Applying `evalElementary m` transports the recurrence
identities, and cancellation is established in the target ring itself.

The stronger certificate is not renamed as the restricted one. The completed
main theorem, positivity, degree, and alphabet compatibility do not depend on
settling restricted-only uniqueness. The old recursive-invariant and staged
implementation plans are [archived](archive/completed-plans/README.md).

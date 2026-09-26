# Circular DN recurrence

The direct contact has strict edges `a → i → z`, with `y = next i`.
The actual `dnSuccessor` raises the row at `y`, lowers the row at `z`,
replaces the strict edges by `a → y → z`, and changes the distinguished
normal edge from `y → z` to `a → i`.

## Checked coloring argument

`Diagram.coloringLLT_dnSuccessor` proves equality of the independently defined
coloring polynomials for every finite alphabet. Its assumptions are the
existing successor-validity hypotheses and `f.tail = e.head`; no symmetry or
polynomial identity remains assumed.

Delete the first strict corner temporarily. This preserves all normal endpoint
pairs and removes exactly its strict pair. The two adjacent boundary values
then agree. The last strict corner's gap excludes every boundary value
congruent to `y`. The existing periodic NN exterior-swap lemmas therefore apply
to this temporary diagram. They establish precisely the background symmetries
needed by the general pair-coloring DN involution. The temporary diagram is
only a geometric auxiliary: its polynomial is not identified with the source.

Related Lean: `../../VerticalStripLLT/Circular/SecondBounceGeometry.lean`,
`CornerBoundary.lean`, `CornerPairs.lean`, and `DNNormalPairs.lean`.

## Checked independent HRV argument

`Diagram.shiftedOrientationExpansion_dnSuccessor` now proves the exact
actual-HRV equality locally. Aristotle supplied the candidate; primary and Luna
ported its reusable lemmas and primary verified every module. The proof uses
the four-state potential identity generalized to any lifted triangle with its
long edge strict. On the source use triangle `(i,y,z)`; on the target use `(a,i,y)`.
For each fixed exterior selected subset, the two middle monomials sum to the
bottom plus the top. Cyclic selections contribute zero.

The weighted four-state sum becomes `(1+q) M00 + q(1+q) M11`.
Top configurations have identical lifted transitive closures. Bottom
configurations correspond under the periodic `i/y` swap of the exterior
subset. The strict outgoing edge at `i` separates source sinks; only order
on sinks, rather than global order preservation, is required for HRV transport.
The argument retains arbitrary winding.

Related Lean: `HRVStepComparison.lean`, `HRVTriangle.lean`,
`OrientationPairSum.lean`, `DNLocalData.lean`, `DNSwapGeometry.lean`,
`DNTargetData.lean`, `DNOrientationBlocks.lean`, and
`SecondBounceOrientation.lean` under `../../VerticalStripLLT/Circular/`.
`Diagram.expansion_iff_secondBounce` combines the independent identities into
an equivalence of the actual semantic bridge for source and target.

## Remaining boundary

Direct DN does not by itself establish full bounce recurrences. Intermediate
DD contacts require auxiliary induction on contact count, using two R1
resolutions and the direct DN move. Some auxiliary diagrams have larger area;
the final area induction cannot justify these intermediate identities.
Generalized ND and its valid area-decreasing successors still require separate
geometric proofs, including possible aliases of edited periodic rows.
The full circular expansion remains open.

# Flip-component proof status

The full ordinary AND circular flip-component HRV formulas now have complete
mathematical proofs. The ordinary word argument was independently audited by
primary, Astra and Terra. The Overleaf v9 bounded-face companion was audited
by primary and Astra and closes every circular case, including primitive
unbalanced components. The component theorems are NOT yet fully formalized.
See the [draft comparison and full circular proof](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md).

The ordinary and full aggregate circular expansions and positivity remain
locally Lean-verified. Their verification boundary has not changed.

The user's request for an easier-to-formalize circular argument is also
resolved mathematically. The [finite companion](proofs/COMPONENT_FINITE_COMPANION.md)
proves the canonical coefficients by ordered-partition cancellation and a
strict-slack edge involution, then isolates whole components using identical
gain graphs. Primary, Astra and Terra audited the proof. No polyhedral,
topological or confluence theorem is needed. The full Lean proof remains pending.

## Complete ordinary component proof

The [ordinary word-algebra proof](proofs/COMPONENT_ORDINARY_PROOF.md) covers
any ordinary natural graph, any subset of strict corners, every complete
component, and every finite alphabet. No saturation, connectivity, forest,
active-uniqueness or recurrence-isolation hypothesis is assumed.

Its component-isolation step is explicit. Let m_C(π) count states in the
ORIGINAL component C compatible with permutation π. For a<b<c in consecutive
word positions, actual flips give the four-word identity

    m_C(ρ acb σ)+m_C(ρ bca σ)
      =m_C(ρ cab σ)+m_C(ρ bac σ).

It allows m_C to pair with a finite word algebra modulo contextual four-word
relations and repeated-letter words. A self-contained conjugation argument
factors the finite coloring product into signed mountain blocks. The two
representatives have coefficients Z_π and j_π, respectively. Their equality
in the quotient gives K(C)=E(C), preserving C throughout. It is NOT a false
pointwise identity Z_π=j_π and does not invoke the aggregate theorem to
separate components.

The proof uses these established ingredients:

| Ingredient | Evidence | Source |
| --- | --- | --- |
| Exact alternating HRV-map coefficients | Audited proof | [HRV differences](proofs/COMPONENT_HRV_DIFFERENCES.md) |
| Normal-edge absorption and exact mixed-closure fibers | Audited proof | [Mixed closure](proofs/COMPONENT_MIXED_CLOSURE.md) |
| Reversed-edge absorption, linear-extension refinement, mountain-block formula | Audited proof | [Labeled mixed posets](proofs/COMPONENT_MIXED_POSET.md) |
| Actual component pairing and finite word-algebra factorization | Independently audited full ordinary proof | [Ordinary component theorem](proofs/COMPONENT_ORDINARY_PROOF.md) |
| Balanced circular components identify with entire ordinary components | Audited proof | [Compatible lifts](proofs/COMPONENT_AMBIENT_REDUCTION.md#compatible-lifts-give-an-exact-ordinary-reduction) |

## What remains

**Lean.** The full component theorems are currently prose. The
[modular integration plan](COMPONENT_FORMALIZATION.md) records the word
quotient, concrete ring and conjugation modules, with primary-owned local
verification of bounded Luna/Terra/Aristotle contributions. The existing component interfaces
are `Circular/Flip.lean` and `Circular/ComponentSemantics.lean`; see
[CIRCULAR_FLIPS.md](CIRCULAR_FLIPS.md). An implementation must prove the actual
component/permutation pairing, both semantic refinements, and the finite
word identities. The additive quotient and induced concatenation are now
verified in `WordRelations`, `WordMultiplication`, and `WordAlgebra`.
`ComponentWords` supplies the full-word count on the actual complete component,
its linear extension, and vanishing on repeated words. The four-term flip
bijection and descent of this particular map to the quotient remain open.
The local geometry, forward/inverse word exchanges, and actual directed-flip
witness now have Lean implementations in `ShortEdges`, `EdgeSwap`, `WordSwap`,
`WordSwapInverse`, `WordCover`, and `WordFlip`.
The verified aggregate expansion does not supply the missing component semantic bridge.

**Circular formalization.** The v9 companion gives a signed expansion in
ENTIRE balanced components. Its coefficient invariance is proved by lifting
a tight-edge flip to an actual flip of the source graph, with the same face.
The HRV-vector identity is separately justified; it is not assumed to be a
polyhedral valuation. This resolves the earlier component-isolation gap.

The user requested a simpler proof to formalize. A direct unbalanced-cycle
deletion recurrence now follows by toggling a strictly slack edge chosen from
the longest-path vector. It terminates at balanced graphs. The independently
audited [finite companion](proofs/COMPONENT_FINITE_COMPANION.md) supplies the
canonical coefficient recurrence and whole-component reconstruction.
Its Lean integration remains open; the mathematical proof is complete.

The [periodic word audit](proofs/COMPONENT_PERIODIC_WORDS.md) remains useful:
it rules out extending the ordinary four-word quotient unchanged, but is no
longer a blocker for the circular theorem. The older winding and aggregate
reductions are alternative tools, not unresolved theorem requirements.

## Earlier induction work and consolidation

The author's minimum-area strategy led to genuine corner-deletion recurrences,
DN transport, mixed-cycle cancellation, normalization and the HRV coefficient
formula used above. The word proof now resolves the ordinary component theorem
without assuming the remaining isolation claims of those alternative routes.
Their stronger auxiliary claims are not automatically proved by the result.

The detailed prior status is [archived at 14e061d](archive/component-status-before-ordinary-word-proof.md).
It preserves the exact failed shortcuts and unproved alternative assertions.
The [documentation index](README.md) retains their proof notes as reusable
research material; they are no longer blockers for the ordinary theorem.
In particular saturation does not preserve a normalized normal-long cover,
and closure-fiber levels need not be whole components. Neither is assumed.

Current ownership, checks and active consultations belong in
[HANDOFF](../HANDOFF.md). Aristotle outcomes remain in [the ledger](ARISTOTLE.md).
No circular component claim is inferred from the completed aggregate theorem.

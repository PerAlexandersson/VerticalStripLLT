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
| Actual ordinary component four-term identity and quotient functional | Locally Lean-verified | [ComponentFunctional](../VerticalStripLLT/Components/ComponentFunctional.lean) |
| Actual component pairing and finite word-algebra factorization | Locally Lean-verified | [Ordinary component theorem](proofs/COMPONENT_ORDINARY_PROOF.md) |
| Compatible ordinary preimage is a union of complete components | Locally Lean-verified | [Compatible lifts](proofs/COMPONENT_AMBIENT_REDUCTION.md#compatible-lifts-give-an-exact-ordinary-reduction) |

## What remains

**Lean.** The full ordinary and circular component identities are not yet
unconditional Lean theorems. Their remaining core lemma is now the per-state HRV
extraction from a literal mountain-word scan. The actual component's quotient
functional, finite Cauchy factorization, contextual scan pairing, HRV threshold
supports, and signed first-block cancellation all compile. The scan semantics
use actual orientation compatibility indicators; no per-state quotient
functional or recurrence-defined substitute is assumed.

The finite circular companion, coefficient constancy, whole-component
undecoration, common balanced potentials, compatible ordinary diagram, actual
orientation/HRV/coloring transports, and forward flip transport are Lean-verified.
`Circular.component_identity_of_forward_components` is the complete conditional
reduction. Its ordinary preimage is a union of complete components, so reverse
flip transport is unnecessary. Finishing ordinary scan extraction and assembly
will discharge its sole ordinary-identity hypothesis.

See the [modular integration plan](COMPONENT_FORMALIZATION.md),
[ComponentScanSemantics](../VerticalStripLLT/Components/ComponentScanSemantics.lean),
and [CircularFromOrdinaryComponents](../VerticalStripLLT/Components/CircularFromOrdinaryComponents.lean).
The aggregate expansion is not used to infer a component identity.

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

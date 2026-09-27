# Flip-component proof status

The full ORDINARY flip-component HRV formula now has a complete mathematical
proof, independently audited by primary, Astra and Terra. By compatible-lift
transport, the same is true for balanced circular components. These component
proofs have NOT yet been formalized in Lean. The formula for unbalanced,
primitive circular components remains open.

The ordinary and full aggregate circular expansions and positivity remain
locally Lean-verified. Their verification boundary has not changed.

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

**Lean.** The new theorem is currently prose. The
[modular integration plan](COMPONENT_FORMALIZATION.md) assigns the additive
word quotient to Luna and isolated conjugation lemmas to Aristotle, with
primary-owned local verification and remaining semantic bridges. The existing component interfaces
are `Circular/Flip.lean` and `Circular/ComponentSemantics.lean`; see
[CIRCULAR_FLIPS.md](CIRCULAR_FLIPS.md). An implementation must prove the actual
component/permutation pairing, both semantic refinements, and the finite
word identities. An additive quotient of finitely supported words with ALL
contexts included is a possible finite implementation; induced concatenation
and its compatibility must be established. The verified aggregate expansion
does not supply the missing component semantic bridge.

**Circular components.** The [winding reduction](proofs/COMPONENT_WINDING_LATTICE.md)
reduces unbalanced connected blocks to primitive circular components. The
new word proof uses one linear vertex order and ordinary forward selected
relations. The [periodic audit](proofs/COMPONENT_PERIODIC_WORDS.md) proves the lifted
HRV-map coefficient formula and the exact circular corrections to the
four-word relation. Negative winding can require cancellation between distinct
HRV maps after elementary evaluation; the ordinary relation itself need not
vanish. These lemmas do not yet give a circular semantic companion. The
[exact winding aggregate](proofs/COMPONENT_LATTICE_AGGREGATE.md) still does
not isolate individual primitive components. The full thread goal remains
active until this case is resolved.

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

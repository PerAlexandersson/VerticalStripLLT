import VerticalStripLLT.Circular.ComponentSemantics

/-!
# Challenge: a shorter proof of the circular component expansion

This file states a proved theorem as a new proof challenge. It imports the
original semantic definitions, not the completed component proof. See
CHALLENGE.md for the rules, reference solution and suggested smaller target.

Prove `circularComponentExpansion`. The proposition is a target, not an axiom
or a claim that a proof has been supplied in this file.
-/

namespace VerticalStripLLT.Challenge

/-- Every complete circular flip component has its actual HRV elementary expansion. -/
def circularComponentExpansion : Prop :=
  ∀ {n : ℕ} (D : Circular.Diagram n) (θ : Circular.Orientation D) (m : ℕ),
    Circular.componentStrictEnumerator D θ m =
      evalElementary m (Circular.componentHRV D θ)

/-- A smaller target: natural edges are forward in the vertex order. -/
def ordinaryComponentExpansion : Prop :=
  ∀ {n : ℕ} (D : Circular.Diagram n),
    (∀ e : Circular.Edge D.area, e.tail < e.head) →
    ∀ (θ : Circular.Orientation D) (m : ℕ),
      Circular.componentStrictEnumerator D θ m =
        evalElementary m (Circular.componentHRV D θ)

end VerticalStripLLT.Challenge

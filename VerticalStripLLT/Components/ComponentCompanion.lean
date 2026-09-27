import VerticalStripLLT.Components.OrientationCompanion
import VerticalStripLLT.Components.ComponentCoefficient
import VerticalStripLLT.Circular.ComponentSemantics

/-! Component sums of the actual finite companion expansions. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The existing HRV fiber expression, applied to an arbitrary integer map. -/
def Diagram.hrvMonomialOfLiftedMap (D : Diagram n) (H : ℤ → ℤ) : EExpansion :=
  ∏ r : Fin n,
    if h : 0 < (Finset.univ.filter fun u : Fin n => D.residue (H u.val) = r).card then
      elementary ⟨(Finset.univ.filter fun u : Fin n => D.residue (H u.val) = r).card, h⟩
    else 1

theorem Orientation.hrvMonomialOfLiftedMap_eq (θ : Orientation D) :
    D.hrvMonomialOfLiftedMap θ.liftedHRV = θ.hrvMonomial := rfl

theorem Orientation.hrvMonomial_companion_all_of_no_strict
    (θ : Orientation D) (hstrict : D.strict = ∅) :
    θ.hrvMonomial = ∑ η : Orientation D,
      D.naturalGain.coefficient (D.strict ∪ θ.val) (D.strict ∪ η.val) • η.hrvMonomial := by
  simpa only [Orientation.hrvMonomialOfLiftedMap_eq] using
    θ.liftedHRV_value_companion_all_of_no_strict hstrict D.hrvMonomialOfLiftedMap

/-- Summing a companion over a component leaves the actual component coefficient. -/
theorem sum_component_companion {M : Type*} [AddCommGroup M]
    (γ : Orientation D) (value : Orientation D → M)
    (hvalue : ∀ α : Orientation D, value α = ∑ η : Orientation D,
      D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) • value η) :
    (∑ α ∈ flipComponent D γ, value α) =
      ∑ η : Orientation D, componentCoefficient D γ η • value η := by
  calc
    (∑ α ∈ flipComponent D γ, value α) =
        ∑ α ∈ flipComponent D γ, ∑ η : Orientation D,
          D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) • value η := by
      apply Finset.sum_congr rfl
      intro α _
      exact hvalue α
    _ = ∑ η : Orientation D, ∑ α ∈ flipComponent D γ,
          D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) • value η := by
      rw [Finset.sum_comm]
    _ = ∑ η : Orientation D, componentCoefficient D γ η • value η := by
      simp only [componentCoefficient, Finset.sum_smul]

theorem componentStrictEnumerator_companion_of_no_strict
    (γ : Orientation D) (hstrict : D.strict = ∅) (m : ℕ) :
    componentStrictEnumerator D γ m = ∑ η : Orientation D,
      componentCoefficient D γ η • D.edgeData.strictOrderEnumerator η.val m :=
  sum_component_companion γ (fun η => D.edgeData.strictOrderEnumerator η.val m)
    (fun η => η.strictOrderEnumerator_companion_all_of_no_strict hstrict m)

theorem component_liftedHRV_value_companion_of_no_strict {M : Type*} [AddCommGroup M]
    (γ : Orientation D) (hstrict : D.strict = ∅) (value : (ℤ → ℤ) → M) :
    (∑ α ∈ flipComponent D γ, value α.liftedHRV) =
      ∑ η : Orientation D, componentCoefficient D γ η • value η.liftedHRV :=
  sum_component_companion γ (fun η => value η.liftedHRV)
    (fun η => η.liftedHRV_value_companion_all_of_no_strict hstrict value)

theorem componentHRV_companion_of_no_strict
    (γ : Orientation D) (hstrict : D.strict = ∅) :
    componentHRV D γ = ∑ η : Orientation D,
      componentCoefficient D γ η • η.hrvMonomial :=
  sum_component_companion γ Orientation.hrvMonomial
    (fun η => η.hrvMonomial_companion_all_of_no_strict hstrict)

theorem componentCoefficient_eq_zero_of_not_balanced (γ θ : Orientation D)
    (hθ : ¬D.naturalGain.Balanced (D.strict ∪ θ.val)) :
    componentCoefficient D γ θ = 0 := by
  apply Finset.sum_eq_zero
  intro α _
  exact D.naturalGain.coefficient_eq_zero_of_not_balanced hθ

end

end VerticalStripLLT.Circular

import VerticalStripLLT.Components.ComponentCompanion
import VerticalStripLLT.Components.ComponentSumPartition
import VerticalStripLLT.Components.UndecoratedComponentSemantics

/-! Reducing the actual circular component identity to complete balanced components. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

variable {n : ℕ} {D : Diagram n}

theorem componentWeight_eq_out (γ : Orientation D) (q : componentClass D) :
    componentWeight D γ q = componentCoefficient D γ q.out := by
  calc
    componentWeight D γ q =
        componentWeight D γ (Quotient.mk (componentSetoid D) q.out) :=
      congrArg (componentWeight D γ) (Quotient.out_eq q).symm
    _ = componentCoefficient D γ q.out := componentWeight_mk γ q.out

theorem componentWeight_eq_zero_of_not_balanced (γ : Orientation D) (q : componentClass D)
    (hq : ¬D.naturalGain.Balanced (D.strict ∪ q.out.val)) :
    componentWeight D γ q = 0 := by
  rw [componentWeight_eq_out]
  exact componentCoefficient_eq_zero_of_not_balanced γ q.out hq

theorem componentStrictEnumerator_grouped_of_no_strict
    (γ : Orientation D) (hstrict : D.strict = ∅) (m : ℕ) :
    componentStrictEnumerator D γ m =
      ∑ q : componentClass D, componentWeight D γ q •
        componentStrictEnumerator D q.out m := by
  rw [componentStrictEnumerator_companion_of_no_strict γ hstrict m]
  exact sum_componentCoefficient_smul γ (fun θ => D.edgeData.strictOrderEnumerator θ.val m)

theorem componentHRV_grouped_of_no_strict (γ : Orientation D) (hstrict : D.strict = ∅) :
    componentHRV D γ = ∑ q : componentClass D,
      componentWeight D γ q • componentHRV D q.out := by
  rw [componentHRV_companion_of_no_strict γ hstrict]
  exact sum_componentCoefficient_smul γ Orientation.hrvMonomial

/-- All unbalanced components vanish from the common signed expansion. The only
remaining semantic input is equality on each complete balanced component. -/
theorem component_identity_of_balanced_components_no_strict
    (γ : Orientation D) (hstrict : D.strict = ∅) (m : ℕ)
    (hbalanced : ∀ θ : Orientation D,
      D.naturalGain.Balanced (D.strict ∪ θ.val) →
        componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ)) :
    componentStrictEnumerator D γ m = evalElementary m (componentHRV D γ) := by
  rw [componentStrictEnumerator_grouped_of_no_strict γ hstrict m,
    componentHRV_grouped_of_no_strict γ hstrict]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : D.naturalGain.Balanced (D.strict ∪ q.out.val)
  · rw [hbalanced q.out hq]
  · rw [componentWeight_eq_zero_of_not_balanced γ q hq]
    simp only [zero_smul]

/-- Original decorated components reduce to balanced components of the same-area
undecorated diagram, using the proved whole-component correspondence. -/
theorem component_identity_of_undecorated_balanced_components
    (γ : Orientation D) (m : ℕ)
    (hbalanced : ∀ θ : Orientation D.undecorated,
      D.undecorated.naturalGain.Balanced (D.undecorated.strict ∪ θ.val) →
        componentStrictEnumerator D.undecorated θ m =
          evalElementary m (componentHRV D.undecorated θ)) :
    componentStrictEnumerator D γ m = evalElementary m (componentHRV D γ) := by
  rw [← componentStrictEnumerator_undecorated γ m, ← componentHRV_undecorated γ]
  exact component_identity_of_balanced_components_no_strict
    γ.toUndecorated rfl m hbalanced

end VerticalStripLLT.Circular

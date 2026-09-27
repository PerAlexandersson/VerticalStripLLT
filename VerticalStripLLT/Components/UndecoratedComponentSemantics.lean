import VerticalStripLLT.Components.UndecoratedComponents
import VerticalStripLLT.Circular.ComponentSemantics

/-! Component-level semantics after forgetting distinguished strict edges. -/

namespace VerticalStripLLT.Circular

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The complete strict-coloring component sum is unchanged by undecoration. -/
theorem componentStrictEnumerator_undecorated (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D.undecorated θ.toUndecorated m =
      componentStrictEnumerator D θ m := by
  simp only [componentStrictEnumerator]
  rw [flipComponent_toUndecorated θ, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro η hη
    exact η.toUndecorated_strictOrderEnumerator m
  · exact Orientation.toUndecorated_injective.injOn

/-- The complete HRV component sum is unchanged by undecoration. -/
theorem componentHRV_undecorated (θ : Orientation D) :
    componentHRV D.undecorated θ.toUndecorated = componentHRV D θ := by
  simp only [componentHRV]
  rw [flipComponent_toUndecorated θ, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro η hη
    exact η.toUndecorated_hrvMonomial
  · exact Orientation.toUndecorated_injective.injOn

end

end VerticalStripLLT.Circular

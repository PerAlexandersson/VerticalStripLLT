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
  simp only [componentStrictEnumerator, flipComponent_toUndecorated θ,
    Finset.sum_image Orientation.toUndecorated_injective.injOn,
    Orientation.toUndecorated_strictOrderEnumerator]

/-- The complete HRV component sum is unchanged by undecoration. -/
theorem componentHRV_undecorated (θ : Orientation D) :
    componentHRV D.undecorated θ.toUndecorated = componentHRV D θ := by
  simp only [componentHRV, flipComponent_toUndecorated θ,
    Finset.sum_image Orientation.toUndecorated_injective.injOn,
    Orientation.toUndecorated_hrvMonomial]

end

end VerticalStripLLT.Circular

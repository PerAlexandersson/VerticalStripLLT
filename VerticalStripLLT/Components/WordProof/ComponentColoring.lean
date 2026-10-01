import VerticalStripLLT.Components.WordProof.ColoringWord
import VerticalStripLLT.Components.WordProof.ComponentScalars

/-! The direct finite strict-coloring refinement inside the actual component. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open scoped BigOperators
open Classical Circular

noncomputable section

variable {n m : ℕ} {D : Diagram n}

/-- A full-word count is the sum of compatibility indicators in the complete component. -/
theorem cast_componentWordCount_eq_sum (K : Type*) [CommRing K]
    (θ : Circular.Orientation D) (w : List (Fin n)) (hw : fullWord w) :
    algebraMap ℤ K (componentWordCount D θ w) =
      ∑ η ∈ flipComponent D θ,
        if wordCompatible (D.edgeData.selected η.val) w then (1 : K) else 0 := by
  rw [componentWordCount_of_full θ hw]
  simp [compatibleComponent, Finset.sum_boole]

/-- Sorting colors increasingly and ties decreasingly gives the strict-coloring refinement. -/
theorem componentStrictEnumerator_eq_coloringWord_sum (θ : Circular.Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m =
      ∑ c : Fin n → Fin m, EdgeData.monomial c *
        algebraMap ℤ (XPoly m) (componentWordCount D θ (coloringWord c)) := by
  rw [componentStrictEnumerator]
  simp_rw [D.edgeData.strictOrderEnumerator_eq_selected_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [cast_componentWordCount_eq_sum (XPoly m) θ _ (fullWord_coloringWord c),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  have hinc : ∀ ⦃u v⦄, D.edgeData.selected η.val u v → u < v := by
    rintro u v ⟨e, _, rfl, rfl⟩
    exact hforward e
  rw [wordCompatible_coloringWord_iff c (D.edgeData.selected η.val) hinc]
  split_ifs <;> simp_all

end

end VerticalStripLLT.Components

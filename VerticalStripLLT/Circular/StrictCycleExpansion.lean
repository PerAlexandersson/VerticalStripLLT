import VerticalStripLLT.Circular.HRV
import VerticalStripLLT.Circular.StrictCycle
import VerticalStripLLT.ShiftEvaluation

/-! The vanishing branch of the circular expansion, for arbitrary diagrams. -/

namespace VerticalStripLLT.Circular

variable {n : ℕ}

theorem shiftedOrientationExpansion_eq_zero_of_strict_incoming (D : Diagram n)
    (hin : ∀ v, ∃ e ∈ D.strict, e.head = v) :
    shiftedOrientationExpansion D = 0 := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, D.area.positive⟩⟩
  let : IsEmpty (Orientation D) := ⟨fun θ =>
    D.edgeData.not_Admissible_of_strict_incoming hin θ.val θ.property.2⟩
  simp [shiftedOrientationExpansion]

/-- Both independently defined sides vanish when every vertex has an incoming strict edge. -/
theorem coloringLLT_shifted_eq_expansion_of_strict_incoming (D : Diagram n)
    (hin : ∀ v, ∃ e ∈ D.strict, e.head = v) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  let : Nonempty (Fin n) := ⟨⟨0, D.area.positive⟩⟩
  rw [Diagram.coloringLLT, D.edgeData.coloringLLT_eq_zero_of_strict_incoming hin m,
    shiftedOrientationExpansion_eq_zero_of_strict_incoming D hin, map_zero, map_zero]

end VerticalStripLLT.Circular

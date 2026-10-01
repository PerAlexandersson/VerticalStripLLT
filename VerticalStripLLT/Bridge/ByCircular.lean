import VerticalStripLLT.Bridge.PathDiagram
import VerticalStripLLT.Circular.Expansion
import VerticalStripLLT.QShiftInjective

/-!
# The Alexandersson–Sulzgruber expansion as the forward case of the circular one

An ordinary path is a forward circular diagram (`SchroderPath.toDiagram`), so the
circular expansion applies to it. This uses neither the recursion of [AS22]
(`SatisfiesRecursion` and its uniqueness theorem) nor the component theorems.
-/

namespace VerticalStripLLT

/-- The ordinary shifted expansion, as the forward case of the circular expansion. -/
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_circular {n : ℕ}
    (P : SchroderPath n) (m : ℕ) :
    xQShift m (coloringLLT P m) = evalElementary m (shiftedOrientationExpansion P) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coloringLLT_size_zero, shiftedOrientationExpansion_size_zero, map_one, map_one]
  · rw [← P.toDiagram_coloringLLT hn, ← P.toDiagram_shiftedOrientationExpansion hn]
    exact Circular.coloringLLT_shifted_eq_eval_shiftedOrientationExpansion _ m

/-- The unshifted expansion of [AS22], by the circular route. -/
theorem coloringLLT_eq_eval_orientationExpansion_by_circular {n : ℕ} (P : SchroderPath n)
    (m : ℕ) : coloringLLT P m = evalElementary m (orientationExpansion P) := by
  apply xQShift_injective m
  rw [coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_circular,
    xQShift_evalElementary_orientationExpansion]

end VerticalStripLLT

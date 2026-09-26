import VerticalStripLLT.OrientationRecursion
import VerticalStripLLT.ColoringCharacterization
import VerticalStripLLT.ReductionRecursionMap
import VerticalStripLLT.ShiftEvaluation
import VerticalStripLLT.OrientationPositive
import VerticalStripLLT.OrientationDegree

namespace VerticalStripLLT

open scoped BigOperators

/-- The ordinary Alexandersson–Sulzgruber expansion, uniformly in every finite alphabet. -/
theorem coloringLLT_eq_eval_orientationExpansion {n : ℕ} (P : SchroderPath n) (m : ℕ) :
    coloringLLT P m = evalElementary m (orientationExpansion P) := by
  apply coloringLLT_eq_of_satisfiesReductionRecursion m
    (fun _ P => evalElementary m (orientationExpansion P))
  simpa only [evalElementary_C, evalElementary_elementaryNat] using
    orientationExpansion_satisfiesReductionRecursion.map (evalElementary m)

/-- Substituting q+1 yields the ascent-weighted elementary orientation formula. -/
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion {n : ℕ}
    (P : SchroderPath n) (m : ℕ) :
    xQShift m (coloringLLT P m) = evalElementary m (shiftedOrientationExpansion P) := by
  rw [coloringLLT_eq_eval_orientationExpansion]
  exact xQShift_evalElementary_orientationExpansion P

/-- The ordinary expansion with its orientation sum exposed. -/
theorem coloringLLT_eq_orientation_sum {n : ℕ} (P : SchroderPath n) (m : ℕ) :
    coloringLLT P m = ∑ θ : Orientation P,
      MvPolynomial.C ((Polynomial.X - 1) ^ orientationAsc P θ) *
        evalElementary m (hrvMonomial θ) := by
  rw [coloringLLT_eq_eval_orientationExpansion]
  simp only [orientationExpansion, orientationExpansionAt, map_sum, map_mul,
    evalElementary_C]

/-- The shifted expansion has the manuscript's q-to-the-number-of-ascents weight. -/
theorem coloringLLT_shifted_eq_orientation_sum {n : ℕ} (P : SchroderPath n) (m : ℕ) :
    xQShift m (coloringLLT P m) = ∑ θ : Orientation P,
      MvPolynomial.C (Polynomial.X ^ orientationAsc P θ) *
        evalElementary m (hrvMonomial θ) := by
  rw [coloringLLT_shifted_eq_eval_shiftedOrientationExpansion]
  simp only [shiftedOrientationExpansion, orientationExpansionAt, map_sum, map_mul,
    evalElementary_C]

/-- One homogeneous elementary expression with nonnegative q-coefficients
represents the shifted coloring polynomial in every finite alphabet. -/
theorem coloringLLT_shifted_e_positive {n : ℕ} (P : SchroderPath n) :
    ∃ f : EExpansion,
      (∀ m, xQShift m (coloringLLT P m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n := by
  exact ⟨shiftedOrientationExpansion P,
    coloringLLT_shifted_eq_eval_shiftedOrientationExpansion P,
    shiftedOrientationExpansion_coeff_nonneg P,
    shiftedOrientationExpansion_isWeightedHomogeneous_degree P⟩

end VerticalStripLLT

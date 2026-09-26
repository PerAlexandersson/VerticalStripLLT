import VerticalStripLLT.Circular.InteriorReversalReduction
import VerticalStripLLT.Circular.NDSeparatedRecurrences
import VerticalStripLLT.Circular.HRVPositive
import VerticalStripLLT.Circular.HRVDegree

/-! The circular LLT expansion in the elementary basis, with nonnegative shifted coefficients. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

/-- The circular coloring polynomial equals its independently defined
integer-cover HRV expansion. -/
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion {n : ℕ}
    (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  exact D.expansion_of_interior_nd_step (interiorNDInductionStep n m)

/-- The circular HRV formula, exposing its elementary monomials and q-ascent weights. -/
theorem coloringLLT_shifted_eq_orientation_sum {n : ℕ} (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) = ∑ θ : Orientation D,
      MvPolynomial.C (Polynomial.X ^ θ.val.card) * evalElementary m θ.hrvMonomial := by
  rw [coloringLLT_shifted_eq_eval_shiftedOrientationExpansion]
  simp only [shiftedOrientationExpansion, map_sum, map_mul, evalElementary_C]

/-- One homogeneous elementary expression with nonnegative q-coefficients
works in every alphabet. -/
theorem coloringLLT_shifted_e_positive {n : ℕ} (D : Diagram n) :
    ∃ f : EExpansion,
      (∀ m, xQShift m (D.coloringLLT m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n := by
  exact ⟨shiftedOrientationExpansion D,
    coloringLLT_shifted_eq_eval_shiftedOrientationExpansion D,
    shiftedOrientationExpansion_coeff_nonneg D,
    shiftedOrientationExpansion_isWeightedHomogeneous_degree D⟩

end VerticalStripLLT.Circular

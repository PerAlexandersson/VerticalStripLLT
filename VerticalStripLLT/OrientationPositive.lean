import VerticalStripLLT.OrientationNatural
import Mathlib.Algebra.Polynomial.Eval.Coeff

namespace VerticalStripLLT

/-- Every coefficient in q of every formal elementary coefficient is nonnegative. -/
theorem shiftedOrientationExpansion_coeff_nonneg {n : ℕ} (P : SchroderPath n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((shiftedOrientationExpansion P).coeff d).coeff j := by
  rw [← naturalCast_naturalOrientationExpansion P]
  simp only [naturalCast, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  exact Nat.cast_nonneg _

end VerticalStripLLT

import VerticalStripLLT.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Operations

namespace VerticalStripLLT

theorem qSubOne_ne_zero : (Polynomial.X - 1 : Q) ≠ 0 := by
  simpa using (Polynomial.X_sub_C_ne_zero (R := ℤ) 1)

theorem qSubOne_C_ne_zero {σ : Type*} :
    (MvPolynomial.C (Polynomial.X - 1) : MvPolynomial σ Q) ≠ 0 := by
  intro h
  apply qSubOne_ne_zero
  exact MvPolynomial.C_injective σ Q (by simpa only [map_zero] using h)

theorem qSubOne_mul_eq_iff {σ : Type*} (f g : MvPolynomial σ Q) :
    MvPolynomial.C (Polynomial.X - 1) * f =
        MvPolynomial.C (Polynomial.X - 1) * g ↔ f = g := by
  constructor
  · exact mul_left_cancel₀ qSubOne_C_ne_zero
  · intro h
    rw [h]

end VerticalStripLLT

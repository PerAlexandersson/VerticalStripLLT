import VerticalStripLLT.ShiftEvaluation

/-! Injectivity and coefficient identities for the polynomial shift q ↦ q + 1. -/

namespace VerticalStripLLT

theorem qShift_injective : Function.Injective qShift := by
  have key : ∀ r : Q, (qShift r).comp (Polynomial.X - 1) = r := by
    intro r
    simp [qShift, Polynomial.comp_assoc]
  intro p q h
  rw [← key p, ← key q, h]

theorem xQShift_injective (m : ℕ) : Function.Injective (xQShift m) :=
  MvPolynomial.map_injective _ qShift_injective

theorem xQShift_C (m : ℕ) (p : Q) :
    xQShift m (MvPolynomial.C p : XPoly m) = MvPolynomial.C (qShift p) := by
  rw [xQShift, MvPolynomial.map_C]

theorem qShift_X : qShift Polynomial.X = Polynomial.X + 1 := by
  simp [qShift]

theorem qShift_X_sub_one : qShift (Polynomial.X - 1) = Polynomial.X := by
  simp [qShift]

theorem C_X_ne_zero_xPoly (m : ℕ) : (MvPolynomial.C Polynomial.X : XPoly m) ≠ 0 :=
  (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero

theorem C_X_ne_zero_eExpansion : (MvPolynomial.C Polynomial.X : EExpansion) ≠ 0 :=
  (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero

end VerticalStripLLT


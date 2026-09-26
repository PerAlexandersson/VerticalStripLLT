import VerticalStripLLT.Circular.HRV
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Natural-coefficient lift and coefficient positivity for the circular HRV expansion. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

abbrev NatEExpansion := MvPolynomial ℕ+ (Polynomial ℕ)

noncomputable def naturalElementary (k : ℕ+) : NatEExpansion := MvPolynomial.X k

noncomputable def naturalHRVMonomial {n : ℕ} {D : Diagram n}
    (θ : Orientation D) : NatEExpansion :=
  ∏ r : Fin n,
    if h : 0 < (Finset.univ.filter fun u => θ.hrv u = r).card then
      naturalElementary ⟨(Finset.univ.filter fun u => θ.hrv u = r).card, h⟩
    else 1

noncomputable def naturalShiftedOrientationExpansion {n : ℕ} (D : Diagram n) : NatEExpansion :=
  ∑ θ : Orientation D,
    MvPolynomial.C (Polynomial.X ^ θ.val.card) * naturalHRVMonomial θ

noncomputable def naturalCast : NatEExpansion →+* EExpansion :=
  MvPolynomial.map (Polynomial.mapRingHom (Nat.castRingHom ℤ))

private theorem naturalCast_elementary (k : ℕ+) :
    naturalCast (naturalElementary k) = elementary k := by
  simp [naturalCast, naturalElementary, elementary]

theorem naturalCast_naturalHRVMonomial {n : ℕ} {D : Diagram n}
    (θ : Orientation D) :
    naturalCast (naturalHRVMonomial θ) = θ.hrvMonomial := by
  classical
  unfold naturalHRVMonomial Orientation.hrvMonomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : 0 < (Finset.univ.filter fun u => θ.hrv u = r).card
  · rw [dite_eq_left h, dite_eq_left h]
    exact naturalCast_elementary _
  · rw [dite_eq_right h, dite_eq_right h]
    exact map_one naturalCast

theorem naturalCast_naturalShiftedOrientationExpansion {n : ℕ} (D : Diagram n) :
    naturalCast (naturalShiftedOrientationExpansion D) = shiftedOrientationExpansion D := by
  classical
  unfold naturalShiftedOrientationExpansion shiftedOrientationExpansion
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro θ _
  rw [map_mul, naturalCast_naturalHRVMonomial]
  congr 1
  rw [naturalCast, MvPolynomial.map_C, map_pow]
  congr 2
  exact Polynomial.map_X (Nat.castRingHom ℤ)

/-- Every coefficient in `q` of every formal elementary coefficient is nonnegative. -/
theorem shiftedOrientationExpansion_coeff_nonneg {n : ℕ} (D : Diagram n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((shiftedOrientationExpansion D).coeff d).coeff j := by
  rw [← naturalCast_naturalShiftedOrientationExpansion D]
  simp only [naturalCast, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  exact Nat.cast_nonneg _

end VerticalStripLLT.Circular

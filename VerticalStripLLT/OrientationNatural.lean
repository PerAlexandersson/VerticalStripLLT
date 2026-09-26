import VerticalStripLLT.OrientationExpansion
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Eval

namespace VerticalStripLLT

open scoped BigOperators

abbrev NEExpansion := MvPolynomial ℕ+ (Polynomial ℕ)

noncomputable def natElementary (k : ℕ+) : NEExpansion := MvPolynomial.X k

noncomputable def natHRVMonomial {n : ℕ} {P : SchroderPath n}
    (θ : Orientation P) : NEExpansion :=
  ∏ r : Fin n, if h : (hrvFiber θ r).Nonempty then
    natElementary ⟨(hrvFiber θ r).card, Finset.card_pos.mpr h⟩ else 1

noncomputable def naturalOrientationExpansion {n : ℕ} (P : SchroderPath n) :
    NEExpansion :=
  ∑ θ : Orientation P,
    MvPolynomial.C (Polynomial.X ^ orientationAsc P θ) * natHRVMonomial θ

noncomputable def naturalCast : NEExpansion →+* EExpansion :=
  MvPolynomial.map (Polynomial.mapRingHom (Nat.castRingHom ℤ))

private theorem naturalCast_elementary (k : ℕ+) :
    naturalCast (natElementary k) = elementary k := by
  simp [naturalCast, natElementary, elementary]

theorem naturalCast_natHRVMonomial {n : ℕ} {P : SchroderPath n}
    (θ : Orientation P) :
    naturalCast (natHRVMonomial θ) = hrvMonomial θ := by
  classical
  unfold natHRVMonomial hrvMonomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  by_cases h : (hrvFiber θ r).Nonempty
  · rw [dite_eq_left h, dite_eq_left h]
    exact naturalCast_elementary _
  · rw [dite_eq_right h, dite_eq_right h]
    exact map_one naturalCast

theorem naturalCast_naturalOrientationExpansion {n : ℕ}
    (P : SchroderPath n) :
    naturalCast (naturalOrientationExpansion P) =
      shiftedOrientationExpansion P := by
  classical
  unfold naturalOrientationExpansion shiftedOrientationExpansion orientationExpansionAt
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [map_mul, naturalCast_natHRVMonomial]
  congr 1
  rw [naturalCast, MvPolynomial.map_C, map_pow]
  congr 2
  exact Polynomial.map_X (Nat.castRingHom ℤ)

end VerticalStripLLT

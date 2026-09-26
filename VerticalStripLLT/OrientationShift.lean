import VerticalStripLLT.OrientationExpansion
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace VerticalStripLLT

open scoped BigOperators

noncomputable def qShift : Q →+* Q :=
  Polynomial.compRingHom (Polynomial.X + 1)

noncomputable def qShiftMap : EExpansion →+* EExpansion :=
  MvPolynomial.map qShift

@[simp] theorem qShift_elementary (k : ℕ+) :
    qShiftMap (elementary k) = elementary k := by
  simp [qShiftMap, elementary]

theorem qShift_hrvMonomial {n : ℕ} {P : SchroderPath n} (θ : Orientation P) :
    qShiftMap (hrvMonomial θ) = hrvMonomial θ := by
  classical
  unfold hrvMonomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  split_ifs
  · exact qShift_elementary _
  · exact map_one qShiftMap

theorem qShift_orientationExpansionAt {n : ℕ} (P : SchroderPath n) (z : Q) :
    qShiftMap (orientationExpansionAt P z) =
      orientationExpansionAt P (qShift z) := by
  classical
  unfold orientationExpansionAt
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [map_mul, qShift_hrvMonomial]
  congr 1
  rw [qShiftMap, MvPolynomial.map_C, map_pow]

theorem qShift_orientationExpansion {n : ℕ} (P : SchroderPath n) :
    qShiftMap (orientationExpansion P) = shiftedOrientationExpansion P := by
  have hz : qShift (Polynomial.X - 1) = Polynomial.X := by
    rw [map_sub, map_one]
    simp only [qShift, Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
      add_sub_cancel_right]
  change qShiftMap (orientationExpansionAt P (Polynomial.X - 1)) =
    orientationExpansionAt P Polynomial.X
  rw [qShift_orientationExpansionAt, hz]

end VerticalStripLLT

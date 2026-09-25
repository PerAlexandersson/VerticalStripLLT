import VerticalStripLLT.OrientationConcatHRV
import Mathlib.Tactic.Ring

namespace VerticalStripLLT

open scoped BigOperators

open OrientationConcat in
theorem orientationExpansionAt_concat {n k : ℕ} (P : SchroderPath n)
    (R : SchroderPath k) (z : Q) :
    orientationExpansionAt (P.concat R) z =
      orientationExpansionAt P z * orientationExpansionAt R z := by
  unfold orientationExpansionAt
  rw [Fintype.sum_equiv (orientationSplit P R) _
    (fun p => MvPolynomial.C (z ^ (orientationAsc P p.1 + orientationAsc R p.2)) *
      (hrvMonomial p.1 * hrvMonomial p.2))
    (fun θ => by rw [orientationSplit_apply, orientationAsc_concat, hrvMonomial_concat]),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [pow_add, map_mul]
  ring

end VerticalStripLLT

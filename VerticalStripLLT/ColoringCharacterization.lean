import VerticalStripLLT.ReductionUniqueness
import VerticalStripLLT.ColoringReductionRecursion
import VerticalStripLLT.PolynomialCancellation

namespace VerticalStripLLT

/-- Any finite-variable invariant with the sufficient reduction certificate
equals the independently defined coloring LLT polynomial. -/
theorem coloringLLT_eq_of_satisfiesReductionRecursion (m : ℕ)
    (F : ∀ n, SchroderPath n → XPoly m)
    (H : SatisfiesReductionRecursion (MvPolynomial.C Polynomial.X)
      (fun k => MvPolynomial.esymm (Fin m) Q k) F)
    {n : ℕ} (P : SchroderPath n) : coloringLLT P m = F n P := by
  have hq : (MvPolynomial.C Polynomial.X - 1 : XPoly m) ≠ 0 := by
    simpa only [map_sub, map_one] using (qSubOne_C_ne_zero (σ := Fin m))
  exact (coloringLLT_satisfiesReductionRecursion m).unique H hq n P

end VerticalStripLLT

import VerticalStripLLT.CyclicHessenberg.Source
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! At shifted parameter zero, every colored cover has weight one. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

noncomputable def specializeQ (m : ℕ) (a : ℤ) :
    XPoly m →+* MvPolynomial (Fin m) ℤ :=
  MvPolynomial.map (Polynomial.evalRingHom a)

/-- At raw parameter one the only multiplicity is the number of canonical covers. -/
theorem specialize_loopColoringLLT_one {k n : ℕ} (h : Tuple k n) (m : ℕ) :
    specializeQ m 1 (loopColoringLLT h m) =
      (Fintype.card (LoopCover h) : MvPolynomial (Fin m) ℤ) *
        (∑ i : Fin m, MvPolynomial.X i) ^ k := by
  classical
  have hsum : (∑ κ : Fin k → Fin m,
      ∏ a : Fin k, (MvPolynomial.X (κ a) : MvPolynomial (Fin m) ℤ)) =
      (∑ i : Fin m, MvPolynomial.X i) ^ k := by
    rw [← Fintype.prod_sum]
    simp
  simp only [loopColoringLLT, map_sum, map_mul, map_prod, specializeQ,
    MvPolynomial.map_C, Polynomial.evalRingHom_apply, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, map_one, one_mul, MvPolynomial.map_X]
  rw [hsum]
  simp [nsmul_eq_mul]

/-- Exact specialization of the independent shifted source, including `k=0` and `m=0`. -/
theorem specialize_shift_cyclicLLT_zero {k n : ℕ} (h : Tuple k n) (m : ℕ) :
    specializeQ m 0 (xQShift m (cyclicLLT h m)) =
      (Fintype.card (LoopCover h) : MvPolynomial (Fin m) ℤ) *
        (∑ i : Fin m, MvPolynomial.X i) ^ k := by
  rw [cyclicLLT_eq_loopColoringLLT]
  have hcomp : (Polynomial.evalRingHom (0 : ℤ)).comp qShift =
      Polynomial.evalRingHom (1 : ℤ) := by
    ext <;> simp [qShift, Polynomial.coe_compRingHom_apply]
  change MvPolynomial.map (Polynomial.evalRingHom (0 : ℤ))
    (MvPolynomial.map qShift (loopColoringLLT h m)) = _
  rw [← MvPolynomial.map_map, hcomp]
  exact specialize_loopColoringLLT_one h m

end VerticalStripLLT.CyclicHessenberg

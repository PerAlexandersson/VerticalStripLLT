import VerticalStripLLT.CyclicHessenberg.Quasisymmetric
import VerticalStripLLT.CyclicHessenberg.SortedLoopSemantics

/-! The literal composition-indexed finite-alphabet source formula. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- Sum over compositions and their sorted loop decompositions, weighted by the usual `M_β`.
This definition uses neither deletion nor the desired elementary expansion. -/
noncomputable def cyclicLLT {k n : ℕ} (h : Tuple k n) (m : ℕ) : XPoly m :=
  ∑ β : Composition k, ∑ D : SortedLoopDecomposition h β,
    MvPolynomial.C (Polynomial.X ^ orderedLoopAscentCount h D.val) *
      monomialQuasisymmetric β m

theorem cyclicLLT_eq_sortedLoopColoringSum {k n : ℕ} (h : Tuple k n) (m : ℕ) :
    cyclicLLT h m = sortedLoopColoringSum h m := by
  simp only [cyclicLLT, sortedLoopColoringSum, runMonomialQuasisymmetric_eq]

/-- The literal source formula equals the independently defined colored-loop polynomial. -/
theorem cyclicLLT_eq_loopColoringLLT {k n : ℕ} (h : Tuple k n) (m : ℕ) :
    cyclicLLT h m = loopColoringLLT h m := by
  rw [cyclicLLT_eq_sortedLoopColoringSum, loopColoringLLT_eq_sortedLoopColoringSum]

theorem shift_cyclicLLT_eq_cyclicExpansion {k n : ℕ}
    (h : Tuple k n) (hn : 0 < n) (m : ℕ) :
    xQShift m (cyclicLLT h m) = evalElementary m (cyclicExpansion h) := by
  rw [cyclicLLT_eq_loopColoringLLT]
  exact shift_loopColoringLLT_eq_cyclicExpansion h hn m

end VerticalStripLLT.CyclicHessenberg

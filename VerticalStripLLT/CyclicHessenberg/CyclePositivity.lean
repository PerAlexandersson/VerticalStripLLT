import VerticalStripLLT.CyclicHessenberg.CycleExpansion
import VerticalStripLLT.CyclicHessenberg.RecursivePositivity

/-! The independent source polynomial equals the explicit sum over canonical cycles. -/

namespace VerticalStripLLT.CyclicHessenberg

noncomputable def naturalCanonicalCyclicExpansion {k n : ℕ} (h : Tuple k n) : NEExpansion :=
  naturalCycleSum (Finset.univ : Finset (Fin k)) (kernelEntry (naturalOpenKernel h))

noncomputable def canonicalCyclicExpansion {k n : ℕ} (h : Tuple k n) : EExpansion :=
  naturalCast (naturalCanonicalCyclicExpansion h)

theorem naturalRecursiveCyclicExpansion_eq_cycleSum {k n : ℕ} (h : Tuple k n) :
    naturalRecursiveCyclicExpansion h = naturalCanonicalCyclicExpansion h :=
  naturalKernelExpansion_eq_cycleSum _ _

theorem recursiveCyclicExpansion_eq_cycleSum {k n : ℕ} (h : Tuple k n) :
    recursiveCyclicExpansion h = canonicalCyclicExpansion h :=
  congrArg naturalCast (naturalRecursiveCyclicExpansion_eq_cycleSum h)

theorem shift_loopColoringLLT_eq_canonicalCycleExpansion {k n : ℕ}
    (h : Tuple k n) (hn : 0 < n) (m : ℕ) :
    xQShift m (loopColoringLLT h m) = evalElementary m (canonicalCyclicExpansion h) := by
  rw [← recursiveCyclicExpansion_eq_cycleSum]
  exact shift_loopColoringLLT_eq_recursiveExpansion h hn m

theorem canonicalCyclicExpansion_coeff_nonneg {k n : ℕ} (h : Tuple k n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) : 0 ≤ ((canonicalCyclicExpansion h).coeff d).coeff j := by
  rw [← recursiveCyclicExpansion_eq_cycleSum]
  exact recursiveCyclicExpansion_coeff_nonneg h d j

theorem canonicalCyclicExpansion_isWeightedHomogeneous {k n : ℕ} (h : Tuple k n) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
      (canonicalCyclicExpansion h) k := by
  rw [← recursiveCyclicExpansion_eq_cycleSum]
  exact recursiveCyclicExpansion_isWeightedHomogeneous h

end VerticalStripLLT.CyclicHessenberg

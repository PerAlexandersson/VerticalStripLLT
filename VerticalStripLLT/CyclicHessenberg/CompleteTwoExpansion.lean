import VerticalStripLLT.CyclicHessenberg.CompleteTwo
import VerticalStripLLT.CyclicHessenberg.TwoVertexExpansion

/-! The complete two-vertex tuple in every positive number of layers. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- For `n+1` complete layers: `(q+2)^n (e₁²+q e₂)`. -/
theorem naturalCyclicExpansion_completeTwo (n : ℕ) :
    naturalCyclicExpansion (completeTwoTuple (n + 1)) =
      MvPolynomial.C ((Polynomial.X + 2) ^ n) *
        (natElementary 1 ^ 2 + MvPolynomial.C Polynomial.X * natElementary 2) := by
  classical
  rw [← naturalCanonicalCyclicExpansion_eq_matchingExpansion,
    ← naturalRecursiveCyclicExpansion_eq_cycleSum]
  unfold naturalRecursiveCyclicExpansion
  have hu : (Finset.univ : Finset (Fin 2)) = {1, 0} := by decide
  have hpair := naturalKernelExpansion_pair (0 : Fin 2) 1 (by decide)
    (kernelEntry (naturalOpenKernel (completeTwoTuple (n + 1))))
  rw [← hu] at hpair
  rw [hpair]
  change MvPolynomial.C (kernelEntry (naturalOpenKernel (completeTwoTuple (n + 1)))
    fullOrderReverseTwo.val fullOrderReverseTwo.val) * natElementary 1 ^ 2 +
    MvPolynomial.C (Polynomial.X *
      kernelEntry (naturalOpenKernel (completeTwoTuple (n + 1)))
        fullOrderReverseTwo.val fullOrderForwardTwo.val) * natElementary 2 = _
  simp only [kernelEntry_order, completeTwoOpenKernel_entry,
    completeTwoLayerKernel_reverse_row, mul_one, map_mul]
  ring

end VerticalStripLLT.CyclicHessenberg

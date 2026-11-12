import VerticalStripLLT.CyclicHessenberg.ExpansionEvaluation
import VerticalStripLLT.CyclicHessenberg.PolynomialSemantics
import VerticalStripLLT.CyclicHessenberg.LayerExchange
import VerticalStripLLT.CyclicHessenberg.ExpansionHomogeneity

/-! The independently defined cyclic loop/color polynomial has a natural elementary expansion.
The explicit cycle and matching descriptions of this recursive witness are separate theorems. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- The positive deletion expression of the independently defined natural transfer product. -/
noncomputable def naturalRecursiveCyclicExpansion {k n : ℕ} (h : Tuple k n) : NEExpansion :=
  naturalKernelExpansion (Finset.univ : Finset (Fin k)) (kernelEntry (naturalOpenKernel h))

noncomputable def recursiveCyclicExpansion {k n : ℕ} (h : Tuple k n) : EExpansion :=
  naturalCast (naturalRecursiveCyclicExpansion h)

/-- Source equality after exactly one shift, in every finite alphabet including the empty one. -/
theorem shift_loopColoringLLT_eq_recursiveExpansion {k n : ℕ} (h : Tuple k n)
    (_hn : 0 < n) (m : ℕ) :
    xQShift m (loopColoringLLT h m) = evalElementary m (recursiveCyclicExpansion h) := by
  have heval := naturalKernelExpansion_eval_eq_weightedKernelColoring
    (Finset.univ : Finset (Fin k)) (kernelEntry (naturalOpenKernel h))
    (naturalOpenKernel_exchangeCompatible h) (kernelEntry_supported _ (naturalOpenKernel h))
    (fun i : Fin m => (MvPolynomial.X i : XPoly m))
    (MvPolynomial.C.comp naturalPolynomialCast)
  rw [recursiveCyclicExpansion, evalElementary_naturalCast_eq_eval₂Hom]
  change xQShift m (loopColoringLLT h m) =
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp naturalPolynomialCast)
      (fun d : ℕ+ => elementaryWeights
        (List.ofFn fun i : Fin m => (MvPolynomial.X i : XPoly m)) d.val)
      (naturalKernelExpansion Finset.univ (kernelEntry (naturalOpenKernel h)))
  rw [heval]
  exact xQShift_loopColoringLLT_eq_naturalOpenKernel_coloring h

/-- Every coefficient of the source's elementary expression is coefficientwise nonnegative. -/
theorem recursiveCyclicExpansion_coeff_nonneg {k n : ℕ} (h : Tuple k n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((recursiveCyclicExpansion h).coeff d).coeff j :=
  kernelExpansion_coeff_nonneg Finset.univ (kernelEntry (naturalOpenKernel h)) d j

theorem recursiveCyclicExpansion_isWeightedHomogeneous {k n : ℕ} (h : Tuple k n) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
      (recursiveCyclicExpansion h) k := by
  simpa only [kernelExpansion, recursiveCyclicExpansion, naturalRecursiveCyclicExpansion,
    Finset.card_univ, Fintype.card_fin] using
    kernelExpansion_isWeightedHomogeneous_degree
      (Finset.univ : Finset (Fin k)) (kernelEntry (naturalOpenKernel h))

/-- A single natural-coefficient elementary expression works in all finite alphabets. -/
theorem loopColoringLLT_has_natural_elementary_expansion {k n : ℕ} (h : Tuple k n)
    (hn : 0 < n) :
    ∃ E : NEExpansion, ∀ m : ℕ,
      xQShift m (loopColoringLLT h m) = evalElementary m (naturalCast E) := by
  refine ⟨naturalRecursiveCyclicExpansion h, ?_⟩
  exact shift_loopColoringLLT_eq_recursiveExpansion h hn

end VerticalStripLLT.CyclicHessenberg

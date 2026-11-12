import VerticalStripLLT.CyclicHessenberg.ColorElementaryWeights
import VerticalStripLLT.CyclicHessenberg.Expansion
import VerticalStripLLT.CyclicHessenberg.LoopSemantics
import VerticalStripLLT.CyclicHessenberg.WeightedColoring
import VerticalStripLLT.ShiftEvaluation

set_option autoImplicit false

/-! Connect the natural elementary expansion to the independently defined source. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- Evaluate a natural elementary expression directly in the finite alphabet. -/
theorem evalElementary_naturalCast_eq_eval₂Hom (m : ℕ)
    (E : VerticalStripLLT.NEExpansion) :
    VerticalStripLLT.evalElementary m (VerticalStripLLT.naturalCast E) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp naturalPolynomialCast)
        (fun d : ℕ+ => elementaryWeights
          (List.ofFn fun i : Fin m => (MvPolynomial.X i : XPoly m)) d.val) E := by
  change MvPolynomial.eval₂Hom MvPolynomial.C
      (fun d : ℕ+ => MvPolynomial.esymm (Fin m) Q d.val)
      (MvPolynomial.map naturalPolynomialCast E) = _
  rw [MvPolynomial.eval₂Hom_map_hom]
  apply MvPolynomial.eval₂Hom_congr
  · rfl
  · funext d
    exact (elementaryWeights_X m d.val).symm
  · rfl

/-- Coefficient maps commute with the coloring enumerator after mapping its kernel. -/
theorem kernelColoringLLT_map_coeff {S : Finset V} (F : Q →+* Q)
    (Z : Kernel Q S) (m : ℕ) :
    MvPolynomial.map F (kernelColoringLLT Z m) =
      weightedKernelColoring S
        (fun l t => (MvPolynomial.C (F (kernelEntry Z l t)) : XPoly m))
        MvPolynomial.X := by
  classical
  calc
    MvPolynomial.map F (kernelColoringLLT Z m) =
        kernelColoringLLT (F.mapMatrix Z) m := by
      simp [kernelColoringLLT, orderColoringEnumerator]
    _ = weightedKernelColoring S
        (fun l t => (MvPolynomial.C (F (kernelEntry Z l t)) : XPoly m))
        MvPolynomial.X := by
      simpa only [kernelEntry_map] using
        (weightedKernelColoring_eq_kernelColoringLLT S (F.mapMatrix Z) m).symm

/-- The loop coloring source equals the coloring sum of the single shifted
natural open-kernel product. -/
theorem xQShift_loopColoringLLT_eq_naturalOpenKernel_coloring
    {k n m : ℕ} (h : Tuple k n) :
    VerticalStripLLT.xQShift m (loopColoringLLT h m) =
      weightedKernelColoring (Finset.univ : Finset (Fin k))
        (fun l t =>
          (MvPolynomial.C
            (naturalPolynomialCast (kernelEntry (naturalOpenKernel h) l t)) : XPoly m))
        MvPolynomial.X := by
  classical
  rw [loopColoringLLT_eq_kernelColoringLLT]
  rw [kernelColoringLLT_map_coeff VerticalStripLLT.qShift (rawOpenKernel h) m]
  have hentry (l t : List (Fin k)) :
      VerticalStripLLT.qShift (kernelEntry (rawOpenKernel h) l t) =
        naturalPolynomialCast (kernelEntry (naturalOpenKernel h) l t) := by
    calc
      VerticalStripLLT.qShift (kernelEntry (rawOpenKernel h) l t) =
          kernelEntry (VerticalStripLLT.qShift.mapMatrix (rawOpenKernel h)) l t := by
        symm
        exact kernelEntry_map VerticalStripLLT.qShift (rawOpenKernel h) l t
      _ = kernelEntry (naturalPolynomialCast.mapMatrix (naturalOpenKernel h)) l t :=
        congrArg (fun K => kernelEntry K l t)
          (cast_naturalOpenKernel_eq_shift_rawOpenKernel h).symm
      _ = naturalPolynomialCast (kernelEntry (naturalOpenKernel h) l t) :=
        kernelEntry_map naturalPolynomialCast (naturalOpenKernel h) l t
  unfold weightedKernelColoring
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [hentry]

end VerticalStripLLT.CyclicHessenberg

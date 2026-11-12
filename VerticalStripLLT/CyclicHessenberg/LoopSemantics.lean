import VerticalStripLLT.CyclicHessenberg.Coloring
import VerticalStripLLT.CyclicHessenberg.LoopWeights
import VerticalStripLLT.CyclicHessenberg.PathKernel

/-! Identify the loop coloring sum with the diagonal kernel coloring enumerator. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n m : ℕ}

/-- Colorings of the full subtype support are the same as colorings of `Fin k`. -/
def finColoringEquiv (k m : ℕ) :
    (Fin k → Fin m) ≃ (↥(Finset.univ : Finset (Fin k)) → Fin m) where
  toFun κ v := κ v.val
  invFun κ a := κ ⟨a, Finset.mem_univ _⟩
  left_inv κ := by
    funext a
    rfl
  right_inv κ := by
    funext a
    rcases a with ⟨a, ha⟩
    rfl

private theorem finColoring_monomial_subtype_eq (κ : Fin k → Fin m) :
    (∏ v : (Finset.univ : Finset (Fin k)), (MvPolynomial.X (κ v.val) : XPoly m)) =
      ∏ a : Fin k, MvPolynomial.X (κ a) := by
  let e : Fin k ≃ (Finset.univ : Finset (Fin k)) :=
    (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)).symm
  exact (Fintype.prod_equiv e
    (fun a : Fin k => MvPolynomial.X (κ a))
    (fun v : (Finset.univ : Finset (Fin k)) => MvPolynomial.X (κ v.val))
    (fun _ => rfl)).symm

private theorem loopColoring_coeff_sum_eq_rawKernel (h : Tuple k n) (m : ℕ)
    (κ : Fin k → Fin m) :
    (∑ L : LoopCover h,
      (MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ) : XPoly m)) =
      MvPolynomial.C
        (rawOpenKernel h (colorSortedFullOrder κ) (colorSortedFullOrder κ)) := by
  classical
  let π := colorSortedFullOrder κ
  let E := loopBoundaryPathEquiv h π
  let f : ClosedLayerPath h π → XPoly m := fun P =>
    MvPolynomial.C (Polynomial.X ^ ∑ ℓ : Fin n,
      layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ))
  calc
    (∑ L : LoopCover h,
        MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ)) =
        ∑ L : LoopCover h, f (E L) := by
      apply Finset.sum_congr rfl
      intro L hL
      change MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ) =
        MvPolynomial.C (Polynomial.X ^ ∑ ℓ : Fin n,
          layerAscentCount (h ℓ)
            ((loopToBoundaryPath h (colorSortedFullOrder κ) L).val ℓ.castSucc)
            ((loopToBoundaryPath h (colorSortedFullOrder κ) L).val ℓ.succ))
      rw [coloredLoopAscentCount_eq_path_sum]
    _ = ∑ P : ClosedLayerPath h π, f P := Equiv.sum_comp E f
    _ = MvPolynomial.C (rawOpenKernel h π π) := by
      rw [rawOpenKernel_diagonal_eq_closedLayerPath_sum]
      simp only [f, map_sum]

private theorem loopColoring_coeff_sum_mul_monomial (h : Tuple k n) (m : ℕ)
    (κ : Fin k → Fin m) :
    (∑ L : LoopCover h,
      MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ)) *
        ∏ a : Fin k, MvPolynomial.X (κ a) =
      MvPolynomial.C
        (rawOpenKernel h (colorSortedFullOrder κ) (colorSortedFullOrder κ)) *
        ∏ a : Fin k, MvPolynomial.X (κ a) := by
  rw [loopColoring_coeff_sum_eq_rawKernel]

/-- The original loop coloring polynomial is the coloring enumerator of the raw
open transfer kernel. -/
theorem loopColoringLLT_eq_kernelColoringLLT (h : Tuple k n) (m : ℕ) :
    loopColoringLLT h m = kernelColoringLLT (rawOpenKernel h) m := by
  classical
  let S : Finset (Fin k) := Finset.univ
  let E := finColoringEquiv k m
  let G : (S → Fin m) → XPoly m := fun c =>
    MvPolynomial.C (rawOpenKernel h (sortColorOrder c) (sortColorOrder c)) *
      ∏ v : S, MvPolynomial.X (c v)
  calc
    (∑ L : LoopCover h, ∑ κ : Fin k → Fin m,
        MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ) *
          ∏ a : Fin k, MvPolynomial.X (κ a)) =
        ∑ κ : Fin k → Fin m, ∑ L : LoopCover h,
          MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ) *
            ∏ a : Fin k, MvPolynomial.X (κ a) := Finset.sum_comm
    _ = ∑ κ : Fin k → Fin m, G (E κ) := by
      apply Finset.sum_congr rfl
      intro κ hκ
      have hsort : sortColorOrder (E κ) = colorSortedFullOrder κ := rfl
      rw [← Finset.sum_mul, loopColoring_coeff_sum_mul_monomial]
      change MvPolynomial.C
          (rawOpenKernel h (colorSortedFullOrder κ) (colorSortedFullOrder κ)) * _ =
        MvPolynomial.C
          (rawOpenKernel h (sortColorOrder (E κ)) (sortColorOrder (E κ))) * _
      rw [hsort]
      congr 1
      exact (finColoring_monomial_subtype_eq κ).symm
    _ = ∑ c : S → Fin m, G c := Equiv.sum_comp E G

end VerticalStripLLT.CyclicHessenberg

import VerticalStripLLT.CyclicHessenberg.FiniteMatrixPaths
import VerticalStripLLT.CyclicHessenberg.LoopKernel

/-! The raw transfer product is the weighted sum over closed feasible layer paths. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators
open Classical

variable {k n : ℕ}

/-- Feasibility of all the layer steps of a fixed-endpoint path. -/
def FixedBoundaryPathFeasible (h : Tuple k n) (π : FullOrder k)
    (p : FixedBoundaryPath (FullOrder k) n π π) : Prop :=
  ∀ ℓ : Fin n, layerFeasible (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)

/-- A feasible fixed-endpoint path is exactly a closed layer path. -/
def fixedBoundaryPathFeasibleEquiv (h : Tuple k n) (π : FullOrder k) :
    {p : FixedBoundaryPath (FullOrder k) n π π // FixedBoundaryPathFeasible h π p} ≃
      ClosedLayerPath h π where
  toFun p := ⟨p.val.val, p.val.property.1, p.val.property.2, p.property⟩
  invFun P :=
    ⟨⟨P.val, ⟨P.property.1, P.property.2.1⟩⟩, P.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    rfl

private theorem fixedBoundaryPath_weight_eq (h : Tuple k n) (π : FullOrder k)
    (p : FixedBoundaryPath (FullOrder k) n π π) :
    (∏ ℓ : Fin n, rawLayerKernel (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)) =
      if hp : FixedBoundaryPathFeasible h π p then
        Polynomial.X ^ ∑ ℓ : Fin n,
          layerAscentCount (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)
      else 0 := by
  classical
  by_cases hp : FixedBoundaryPathFeasible h π p
  · rw [dite_eq_left hp]
    simp_rw [rawLayerKernel, layerKernelAt, if_pos (hp _)]
    rw [Finset.prod_pow_eq_pow_sum]
  · rw [dite_eq_right hp]
    have hex : ∃ ℓ : Fin n, ¬ layerFeasible (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ) :=
      not_forall.mp hp
    obtain ⟨ℓ, hℓ⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
    simp [rawLayerKernel, layerKernelAt, hℓ]

/-- The diagonal raw open kernel counts closed boundary paths by their total
layer ascent exponent. -/
theorem rawOpenKernel_diagonal_eq_closedLayerPath_sum (h : Tuple k n)
    (π : FullOrder k) :
    rawOpenKernel h π π =
      ∑ P : ClosedLayerPath h π,
        Polynomial.X ^ ∑ ℓ : Fin n,
          layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ) := by
  classical
  let M : Fin n → Matrix (FullOrder k) (FullOrder k) Q :=
    fun ℓ => rawLayerKernel (h ℓ)
  have hpath := list_prod_eq_sum_fixedBoundaryPath M π π
  change (List.ofFn fun ℓ : Fin n => rawLayerKernel (h ℓ)).prod π π = _
  change (List.ofFn M).prod π π = _
  rw [hpath]
  dsimp only [M]
  simp_rw [fixedBoundaryPath_weight_eq]
  let E := fixedBoundaryPathFeasibleEquiv h π
  let w : FixedBoundaryPath (FullOrder k) n π π → Q := fun p =>
    Polynomial.X ^ ∑ ℓ : Fin n,
      layerAscentCount (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)
  have hsubtype :
      (∑ p : FixedBoundaryPath (FullOrder k) n π π,
        if hp : FixedBoundaryPathFeasible h π p then w p else 0) =
      ∑ p : {p : FixedBoundaryPath (FullOrder k) n π π //
          FixedBoundaryPathFeasible h π p}, w p.val := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (FixedBoundaryPathFeasible h π)
      (fun p : FixedBoundaryPath (FullOrder k) n π π =>
        if hp : FixedBoundaryPathFeasible h π p then w p else 0)
    have hyes : (∑ p : {p : FixedBoundaryPath (FullOrder k) n π π //
        FixedBoundaryPathFeasible h π p},
        if hp : FixedBoundaryPathFeasible h π p.val then w p.val else 0) =
          ∑ p : {p : FixedBoundaryPath (FullOrder k) n π π //
            FixedBoundaryPathFeasible h π p}, w p.val := by
      apply Finset.sum_congr rfl
      intro p hp
      exact dite_eq_left p.property
    have hno : (∑ p : {p : FixedBoundaryPath (FullOrder k) n π π //
        ¬ FixedBoundaryPathFeasible h π p},
        if hp : FixedBoundaryPathFeasible h π p.val then w p.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact dite_eq_right p.property
    rw [hyes, hno, add_zero] at hsplit
    exact hsplit.symm
  calc
    (∑ p : FixedBoundaryPath (FullOrder k) n π π,
        if hp : FixedBoundaryPathFeasible h π p then w p else 0) =
        ∑ p : {p : FixedBoundaryPath (FullOrder k) n π π //
            FixedBoundaryPathFeasible h π p}, w p.val := hsubtype
    _ = ∑ P : ClosedLayerPath h π, w (E.symm P).val := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.sum_comp E (fun p => w (E.symm p).val)
    _ = ∑ P : ClosedLayerPath h π,
          Polynomial.X ^ ∑ ℓ : Fin n,
            layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ) := by
      apply Finset.sum_congr rfl
      intro P hP
      simp [w, E, fixedBoundaryPathFeasibleEquiv]

end VerticalStripLLT.CyclicHessenberg

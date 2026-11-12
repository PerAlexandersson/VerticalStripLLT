import VerticalStripLLT.CyclicHessenberg.MatchingPaths

/-! The natural transfer product is the weighted sum over open feasible paths. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators
open Classical

variable {k n : ℕ}

/-- Feasibility of every layer step of a path with prescribed endpoints. -/
def OpenFixedBoundaryPathFeasible (h : Tuple k n) (π τ : FullOrder k)
    (p : FixedBoundaryPath (FullOrder k) n π τ) : Prop :=
  ∀ ℓ : Fin n, layerFeasible (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)

/-- A feasible fixed-endpoint path is exactly an open layer path. -/
def openFixedBoundaryPathFeasibleEquiv (h : Tuple k n) (π τ : FullOrder k) :
    {p : FixedBoundaryPath (FullOrder k) n π τ //
        OpenFixedBoundaryPathFeasible h π τ p} ≃ OpenLayerPath h π τ where
  toFun p := ⟨p.val.val, p.val.property.1, p.val.property.2, p.property⟩
  invFun P := ⟨⟨P.val, ⟨P.property.1, P.property.2.1⟩⟩, P.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    rfl

private theorem openFixedBoundaryPath_weight_eq (h : Tuple k n) (π τ : FullOrder k)
    (p : FixedBoundaryPath (FullOrder k) n π τ) :
    (∏ ℓ : Fin n,
      naturalLayerKernel (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)) =
      if hp : OpenFixedBoundaryPathFeasible h π τ p then
        (1 + Polynomial.X) ^ ∑ ℓ : Fin n,
          layerAscentCount (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)
      else 0 := by
  by_cases hp : OpenFixedBoundaryPathFeasible h π τ p
  · rw [dite_eq_left hp]
    simp_rw [naturalLayerKernel, layerKernelAt, if_pos (hp _)]
    rw [Finset.prod_pow_eq_pow_sum]
  · rw [dite_eq_right hp]
    obtain ⟨ℓ, hℓ⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
    simp [naturalLayerKernel, layerKernelAt, hℓ]

/-- The natural open kernel counts feasible paths with `(1+q)` to the total
layer ascent count. -/
theorem naturalOpenKernel_eq_openLayerPath_sum (h : Tuple k n)
    (π τ : FullOrder k) :
    naturalOpenKernel h π τ =
      ∑ P : OpenLayerPath h π τ,
        (1 + Polynomial.X) ^ ∑ ℓ : Fin n,
          layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ) := by
  let M : Fin n → Matrix (FullOrder k) (FullOrder k) (Polynomial ℕ) :=
    fun ℓ => naturalLayerKernel (h ℓ)
  have hpath := list_prod_eq_sum_fixedBoundaryPath M π τ
  change (List.ofFn fun ℓ : Fin n => naturalLayerKernel (h ℓ)).prod π τ = _
  change (List.ofFn M).prod π τ = _
  rw [hpath]
  dsimp only [M]
  simp_rw [openFixedBoundaryPath_weight_eq]
  let E := openFixedBoundaryPathFeasibleEquiv h π τ
  let w : FixedBoundaryPath (FullOrder k) n π τ → Polynomial ℕ := fun p =>
    (1 + Polynomial.X) ^ ∑ ℓ : Fin n,
      layerAscentCount (h ℓ) (p.val ℓ.castSucc) (p.val ℓ.succ)
  have hsubtype :
      (∑ p : FixedBoundaryPath (FullOrder k) n π τ,
        if hp : OpenFixedBoundaryPathFeasible h π τ p then w p else 0) =
      ∑ p : {p : FixedBoundaryPath (FullOrder k) n π τ //
          OpenFixedBoundaryPathFeasible h π τ p}, w p.val := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (OpenFixedBoundaryPathFeasible h π τ)
      (fun p : FixedBoundaryPath (FullOrder k) n π τ =>
        if hp : OpenFixedBoundaryPathFeasible h π τ p then w p else 0)
    have hyes :
        (∑ p : {p : FixedBoundaryPath (FullOrder k) n π τ //
            OpenFixedBoundaryPathFeasible h π τ p},
          if hp : OpenFixedBoundaryPathFeasible h π τ p.val then w p.val else 0) =
        ∑ p : {p : FixedBoundaryPath (FullOrder k) n π τ //
            OpenFixedBoundaryPathFeasible h π τ p}, w p.val := by
      apply Finset.sum_congr rfl
      intro p hp
      exact dite_eq_left p.property
    have hno :
        (∑ p : {p : FixedBoundaryPath (FullOrder k) n π τ //
            ¬ OpenFixedBoundaryPathFeasible h π τ p},
          if hp : OpenFixedBoundaryPathFeasible h π τ p.val then w p.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact dite_eq_right p.property
    rw [hyes, hno, add_zero] at hsplit
    exact hsplit.symm
  calc
    (∑ p : FixedBoundaryPath (FullOrder k) n π τ,
        if hp : OpenFixedBoundaryPathFeasible h π τ p then w p else 0) =
        ∑ p : {p : FixedBoundaryPath (FullOrder k) n π τ //
            OpenFixedBoundaryPathFeasible h π τ p}, w p.val := hsubtype
    _ = ∑ P : OpenLayerPath h π τ, w (E.symm P).val := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.sum_comp E (fun p => w (E.symm p).val)
    _ = ∑ P : OpenLayerPath h π τ,
          (1 + Polynomial.X) ^ ∑ ℓ : Fin n,
            layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ) := by
      apply Finset.sum_congr rfl
      intro P hP
      simp [w, E, openFixedBoundaryPathFeasibleEquiv]

end VerticalStripLLT.CyclicHessenberg

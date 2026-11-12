import VerticalStripLLT.CyclicHessenberg.Loops
import VerticalStripLLT.CyclicHessenberg.Layer

/-! The semantic bridge begins with a bijection from canonical covers to closed boundary paths. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k n : ℕ}

/-- Identify positions of a full boundary order with `Fin k`. -/
def layerPositionEquiv (k : ℕ) : LayerPosition k ≃ Fin k := finCongr (by simp)

/-- Boundary lists and permutations are equivalent, preserving their position convention. -/
def fullOrdersPerm (k : ℕ) : FullOrder k ≃ Equiv.Perm (Fin k) :=
  (ordersEquiv Finset.univ).trans
    (Equiv.equivCongr (layerPositionEquiv k)
      (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)))

@[simp] theorem fullOrdersPerm_apply_position (π : FullOrder k) (i : LayerPosition k) :
    fullOrdersPerm k π (layerPositionEquiv k i) = (orderEquiv π i).val := by
  change (orderEquiv π ((layerPositionEquiv k).symm (layerPositionEquiv k i))).val = _
  rw [Equiv.symm_apply_apply]

theorem layerFeasible_iff_permutations (h : Hessenberg k) (π τ : FullOrder k) :
    layerFeasible h π τ ↔
      ∀ i : Fin k, fullOrdersPerm k π i ≤ h (fullOrdersPerm k τ i) := by
  constructor
  · intro hf i
    have hh := hf ((layerPositionEquiv k).symm i)
    rw [← fullOrdersPerm_apply_position, ← fullOrdersPerm_apply_position,
      Equiv.apply_symm_apply] at hh
    exact hh
  · intro hf i
    simpa using hf (layerPositionEquiv k i)

/-- Closed paths of boundary orders with their original edge-feasibility conditions. -/
def IsClosedLayerPath (h : Tuple k n) (π : FullOrder k)
    (P : Fin (n + 1) → FullOrder k) : Prop :=
  P 0 = π ∧ P (Fin.last n) = π ∧
    ∀ ℓ : Fin n, layerFeasible (h ℓ) (P ℓ.castSucc) (P ℓ.succ)

abbrev ClosedLayerPath (h : Tuple k n) (π : FullOrder k) :=
  {P : Fin (n + 1) → FullOrder k // IsClosedLayerPath h π P}

noncomputable instance closedLayerPathFintype (h : Tuple k n) (π : FullOrder k) :
    Fintype (ClosedLayerPath h π) := Fintype.ofFinite _

/-- Reorder every layer of a canonical cover by a fixed first-boundary order. -/
def loopToBoundaryPath (h : Tuple k n) (π : FullOrder k) (L : LoopCover h) :
    ClosedLayerPath h π := by
  refine ⟨fun ℓ => (fullOrdersPerm k).symm ((fullOrdersPerm k π).trans (L.val ℓ)),
    ?_, ?_, ?_⟩
  · simp [L.property.1]
  · simp [L.property.2.1]
  · intro ℓ
    rw [layerFeasible_iff_permutations]
    intro i
    simpa using L.property.2.2 ℓ (fullOrdersPerm k π i)

/-- Recover the canonical label by following its position in the first boundary. -/
def boundaryPathToLoop (h : Tuple k n) (π : FullOrder k) (P : ClosedLayerPath h π) :
    LoopCover h := by
  refine ⟨fun ℓ => (fullOrdersPerm k π).symm.trans (fullOrdersPerm k (P.val ℓ)),
    ?_, ?_, ?_⟩
  · dsimp only
    rw [P.property.1]
    exact Equiv.symm_trans_self _
  · dsimp only
    rw [P.property.2.1]
    exact Equiv.symm_trans_self _
  · intro ℓ a
    exact (layerFeasible_iff_permutations _ _ _).mp (P.property.2.2 ℓ)
      ((fullOrdersPerm k π).symm a)

/-- This bijection is independent of any expansion or positivity statement. -/
def loopBoundaryPathEquiv (h : Tuple k n) (π : FullOrder k) :
    LoopCover h ≃ ClosedLayerPath h π where
  toFun := loopToBoundaryPath h π
  invFun := boundaryPathToLoop h π
  left_inv L := by
    apply Subtype.ext
    funext ℓ
    apply Equiv.ext
    intro a
    simp [boundaryPathToLoop, loopToBoundaryPath]
  right_inv P := by
    apply Subtype.ext
    funext ℓ
    apply (fullOrdersPerm k).injective
    apply Equiv.ext
    intro i
    simp [boundaryPathToLoop, loopToBoundaryPath]

end VerticalStripLLT.CyclicHessenberg

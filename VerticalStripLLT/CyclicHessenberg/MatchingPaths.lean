import VerticalStripLLT.CyclicHessenberg.Matchings
import VerticalStripLLT.CyclicHessenberg.LoopKernel
import VerticalStripLLT.CyclicHessenberg.FiniteMatrixPaths

/-! Actual matching tuples with specified monodromy are open feasible boundary paths. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k n : ℕ}

def IsOpenLayerPath (h : Tuple k n) (π τ : FullOrder k)
    (P : Fin (n + 1) → FullOrder k) : Prop :=
  P 0 = π ∧ P (Fin.last n) = τ ∧
    ∀ ℓ : Fin n, layerFeasible (h ℓ) (P ℓ.castSucc) (P ℓ.succ)

abbrev OpenLayerPath (h : Tuple k n) (π τ : FullOrder k) :=
  {P : Fin (n + 1) → FullOrder k // IsOpenLayerPath h π τ P}

noncomputable instance openLayerPathFintype (h : Tuple k n) (π τ : FullOrder k) :
    Fintype (OpenLayerPath h π τ) := Fintype.ofFinite _

abbrev MatchingFiber (h : Tuple k n) (p : Equiv.Perm (Fin k)) :=
  {φ : MatchingTuple h // matchingMonodromy φ.val = p}

noncomputable instance matchingFiberFintype (h : Tuple k n) (p : Equiv.Perm (Fin k)) :
    Fintype (MatchingFiber h p) := Fintype.ofFinite _

def matchingToOpenPath (h : Tuple k n) (π τ : FullOrder k)
    (φ : MatchingFiber h ((fullOrdersPerm k π).symm.trans (fullOrdersPerm k τ))) :
    OpenLayerPath h π τ := by
  refine ⟨fun ℓ => (fullOrdersPerm k).symm
    ((fullOrdersPerm k π).trans (matchingTransport φ.val.val ℓ)), ?_, ?_, ?_⟩
  · apply (fullOrdersPerm k).injective
    rw [Equiv.apply_symm_apply]
    ext x
    simp
  · change (fullOrdersPerm k).symm
      ((fullOrdersPerm k π).trans (matchingMonodromy φ.val.val)) = τ
    rw [φ.property]
    apply (fullOrdersPerm k).injective
    rw [Equiv.apply_symm_apply]
    ext x
    simp
  · intro ℓ
    rw [layerFeasible_iff_permutations]
    intro i
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply, matchingTransport_succ_apply]
      using φ.val.property ℓ (matchingTransport φ.val.val ℓ.castSucc (fullOrdersPerm k π i))

def openPathToMatching (h : Tuple k n) (π τ : FullOrder k)
    (P : OpenLayerPath h π τ) :
    MatchingFiber h ((fullOrdersPerm k π).symm.trans (fullOrdersPerm k τ)) := by
  refine ⟨⟨fun ℓ => (fullOrdersPerm k (P.val ℓ.castSucc)).symm.trans
    (fullOrdersPerm k (P.val ℓ.succ)), ?_⟩, ?_⟩
  · intro ℓ x
    have hh := (layerFeasible_iff_permutations _ _ _).mp (P.property.2.2 ℓ)
      ((fullOrdersPerm k (P.val ℓ.castSucc)).symm x)
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using hh
  · change matchingTransport
      (fun ℓ => (fullOrdersPerm k (P.val ℓ.castSucc)).symm.trans
        (fullOrdersPerm k (P.val ℓ.succ))) (Fin.last n) = _
    rw [matchingTransport_of_arbitrary_boundaries (fun ℓ => fullOrdersPerm k (P.val ℓ)),
      P.property.1, P.property.2.1]

def matchingOpenPathEquiv (h : Tuple k n) (π τ : FullOrder k) :
    MatchingFiber h ((fullOrdersPerm k π).symm.trans (fullOrdersPerm k τ)) ≃
      OpenLayerPath h π τ where
  toFun := matchingToOpenPath h π τ
  invFun := openPathToMatching h π τ
  left_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    funext ℓ
    apply Equiv.ext
    intro x
    simp only [openPathToMatching, matchingToOpenPath, Equiv.apply_symm_apply,
      Equiv.trans_apply, Equiv.symm_trans_apply, matchingTransport_succ_apply]
  right_inv P := by
    apply Subtype.ext
    funext ℓ
    apply (fullOrdersPerm k).injective
    simp only [matchingToOpenPath, openPathToMatching, Equiv.apply_symm_apply]
    rw [matchingTransport_of_arbitrary_boundaries (fun ℓ => fullOrdersPerm k (P.val ℓ)),
      P.property.1]
    ext x
    simp

end VerticalStripLLT.CyclicHessenberg

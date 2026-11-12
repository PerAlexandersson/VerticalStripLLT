import VerticalStripLLT.CyclicHessenberg.MatchingPaths

/-! Canonically labelled loop covers are exactly matching tuples with identity monodromy. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {k n : ℕ}

def loopCoverToMatching (h : Tuple k n) (L : LoopCover h) : MatchingFiber h 1 := by
  refine ⟨⟨fun ℓ => (L.val ℓ.castSucc).symm.trans (L.val ℓ.succ), ?_⟩, ?_⟩
  · intro ℓ x
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
      L.property.2.2 ℓ ((L.val ℓ.castSucc).symm x)
  · change matchingTransport _ (Fin.last n) = 1
    rw [matchingTransport_of_boundaries L.val L.property.1, L.property.2.1]
    rfl

def matchingToLoopCover (h : Tuple k n) (φ : MatchingFiber h 1) : LoopCover h := by
  refine ⟨matchingTransport φ.val.val, matchingTransport_zero _, φ.property, ?_⟩
  intro ℓ a
  rw [matchingTransport_succ_apply]
  exact φ.val.property ℓ (matchingTransport φ.val.val ℓ.castSucc a)

def loopCoverMatchingEquiv (h : Tuple k n) : LoopCover h ≃ MatchingFiber h 1 where
  toFun := loopCoverToMatching h
  invFun := matchingToLoopCover h
  left_inv L := by
    apply Subtype.ext
    funext i
    exact matchingTransport_of_boundaries L.val L.property.1 i
  right_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    funext ℓ
    exact matchingTransport_recover φ.val.val ℓ

theorem card_loopCover_eq_card_identityMatchingFiber (h : Tuple k n) :
    Fintype.card (LoopCover h) = Fintype.card (MatchingFiber h 1) :=
  Fintype.card_congr (loopCoverMatchingEquiv h)

end VerticalStripLLT.CyclicHessenberg

import VerticalStripLLT.Circular.DNReduction

/-! Full DN as the area-preserving branch of the semantic induction. -/

namespace VerticalStripLLT.Circular.Diagram

/-- The actual DN successor preserves area and lowers the secondary strict rank. -/
theorem expansion_of_dn {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounce D t x) (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea = D.doubledArea →
      Q.strictRank < D.strictRank → xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨Q, _, harea, hrank, hcolor, horient⟩ := D.exists_dn_reduction ha ht h hx hx1
  rw [hcolor m, horient]
  exact ih Q harea hrank

end VerticalStripLLT.Circular.Diagram

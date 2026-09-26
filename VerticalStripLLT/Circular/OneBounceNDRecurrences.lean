import VerticalStripLLT.Circular.OneBounceND

/-! The direct ND branch of half-square area induction, for the actual two models. -/

namespace VerticalStripLLT.Circular.Diagram

namespace NDLocalData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

theorem expansion_of_targets (m : ℕ)
    (hQ : xQShift m (B.shortened.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.shortened))
    (hR : xQShift m (B.ndR.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.ndR)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  rw [B.xQShift_coloringLLT_nd, B.shiftedOrientationExpansion_nd]
  simp only [map_add, map_mul, evalElementary_C, hQ, hR]

end NDLocalData

/-- Both targets of the direct ND relation are supplied by the outer area induction. -/
theorem expansion_of_oneBounce_nd {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨B⟩ := D.exists_ndLocalData ht h hx hx1
  apply B.expansion_of_targets m
  · apply ih B.shortened
    have := B.shortened_doubledArea
    lia
  · apply ih B.ndR
    have := B.ndR_doubledArea
    lia

end VerticalStripLLT.Circular.Diagram

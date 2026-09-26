import VerticalStripLLT.Circular.DDResolvedMeasure

/-! Semantic assembly for the actual DD resolution. The resolved child can
have larger half-square area, so its equality is an explicit separate input. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem expansion_of_children (m : ℕ)
    (hresolved : xQShift m (B.resolved.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.resolved))
    (hdeleted : xQShift m (B.deleted.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.deleted)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  have hq : (MvPolynomial.C Polynomial.X : XPoly m) ≠ 0 := by
    intro h
    apply Polynomial.X_ne_zero (R := ℤ)
    exact MvPolynomial.C_injective (Fin m) Q (by simpa only [map_zero] using h)
  apply mul_left_cancel₀ hq
  rw [B.coloring_resolution m, hresolved, hdeleted]
  have h := congrArg (evalElementary m) B.orientation_resolution
  simpa only [map_mul, map_sub, evalElementary_C] using h.symm

/-- Outer area induction supplies only the deletion child. Local elimination
must establish the resolved child's equality before this lemma applies. -/
theorem expansion_of_resolved (m : ℕ)
    (hresolved : xQShift m (B.resolved.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.resolved))
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  apply B.expansion_of_children m hresolved
  apply ih B.deleted
  have h := B.deleted_doubledArea
  lia

end VerticalStripLLT.Circular.Diagram.DDLocalData

import VerticalStripLLT.Circular.ComponentFactorization
import VerticalStripLLT.Circular.InteriorComponentPaths
import VerticalStripLLT.Circular.NDInductionCases

/-! Column reversal discharges the full interior-overlap induction step. -/

namespace VerticalStripLLT.Circular

namespace Diagram.InteriorMergedComponent

variable {n r j : ℕ} {D : Diagram n} {t : ℤ} (K : Diagram.InteriorMergedComponent D t r j)

/-- Cancellation of the target's forced factor transfers the actual expansion to the source. -/
theorem expansion_of_reversalTarget (m : ℕ)
    (ih : xQShift m (K.reversalTarget.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion K.reversalTarget)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  apply (D.expansion_iff_component_residual K.componentVertices
    (fun u hu v hv hne => K.component_strict_total u v hu hv hne) m).mpr
  have h := (K.reversalTarget.expansion_iff_component_residual K.componentVertices
    (fun u hu v hv hne => K.reversalTarget_component_strict_total u v hu hv hne) m).mp ih
  rw [K.coloringLLT_exterior_reversal m, ← K.orientSum_exterior_reversal] at h
  exact h

end Diagram.InteriorMergedComponent

/-- Every interior contact has a strictly smaller target with the same semantic bridge. -/
theorem Diagram.expansion_of_nd_interior_overlap {n : ℕ} (D : Diagram n)
    {t x : ℤ} {k : ℕ} (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1)) (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hinner : ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) = evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨i, hi1, hik, hires⟩ := hinner
  obtain ⟨K⟩ := Diagram.exists_interiorMergedComponent_of_overlap ha ht h hx hx1 hi1 hik hires
  exact K.expansion_of_reversalTarget m (ih K.reversalTarget K.reversalTarget_doubledArea_lt)

/-- The last input to the checked outer area induction is proved. -/
theorem interiorNDInductionStep (n m : ℕ) : InteriorNDInductionStep n m := by
  intro D t x k _ ha ht h hx hx1 hinner ih
  exact D.expansion_of_nd_interior_overlap ha ht h hx hx1 hinner m
    (fun Q hQ => ih Q (Or.inl hQ))

end VerticalStripLLT.Circular

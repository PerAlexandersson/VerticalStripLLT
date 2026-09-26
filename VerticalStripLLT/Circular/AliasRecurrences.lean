import VerticalStripLLT.Circular.AliasReductionOrient

/-! Actual polynomial identities and the induction step for overlapping ND contacts. -/

namespace VerticalStripLLT.Circular.AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem target_admissible_iff :
    K.target.edgeData.Admissible ∅ ↔ D.edgeData.Admissible ∅ := by
  have h := K.transport_admissible ∅ (Finset.empty_subset _)
  simpa [Diagram.edgesOfPairs] using h.symm

theorem shifted_coloring_identity (m : ℕ) :
    xQShift m (D.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m (K.target.coloringLLT m) := by
  rw [K.coloring_identity m, map_mul]
  congr 1
  simpa using xQShift_C_X_pow' m 1

theorem expansion_of_target (m : ℕ)
    (ih : xQShift m (K.target.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion K.target)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  rw [K.shifted_coloring_identity, K.orient_identity, map_mul, evalElementary_C, ih]

end VerticalStripLLT.Circular.AliasContacts

namespace VerticalStripLLT.Circular.Diagram

theorem exists_nd_alias_reduction {n : ℕ} (D : Diagram n)
    (ha : D.edgeData.Admissible ∅) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounce D t x)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (halias : D.residue t = D.residue (x + 1)) :
    ∃ Q : Diagram n, Q.doubledArea + 6 = D.doubledArea ∧
      (∀ m : ℕ, D.coloringLLT m = MvPolynomial.C Polynomial.X * Q.coloringLLT m) ∧
      shiftedOrientationExpansion D =
        MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion Q := by
  obtain ⟨K, _, _⟩ := D.aliasContacts_of_reverseBounce ha ht h hx hx1 halias
  refine ⟨K.target, ?_, K.coloring_identity, K.orient_identity⟩
  exact D.aliasTarget_doubledArea _ _ _ _ _ _ _ _

/-- The actual alias successor discharges this branch of area induction. -/
theorem expansion_of_nd_alias {n : ℕ} (D : Diagram n)
    (ha : D.edgeData.Admissible ∅) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounce D t x)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (halias : D.residue t = D.residue (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      Q.edgeData.Admissible ∅ → xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨K, _, _⟩ := D.aliasContacts_of_reverseBounce ha ht h hx hx1 halias
  apply K.expansion_of_target m
  apply ih K.target
  · have harea : K.target.doubledArea + 6 = D.doubledArea :=
      D.aliasTarget_doubledArea _ _ _ _ _ _ _ _
    lia
  · exact K.target_admissible_iff.mpr ha

end VerticalStripLLT.Circular.Diagram

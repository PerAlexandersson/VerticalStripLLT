import VerticalStripLLT.Circular.NDSeparatedRelations
import VerticalStripLLT.Circular.NDInductionCases

/-! The proved separated ND reduction supplies its outer-induction input. -/

namespace VerticalStripLLT.Circular

open Diagram

/-- Separated ND reduces the semantic bridge to two strictly smaller areas. -/
theorem Diagram.expansion_of_nd_separated {n : ℕ} (D : Diagram n)
    {t x : ℤ} {k : ℕ} (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x k) (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hsep : ∀ i ≤ k, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨Q, R, hQ, hR, hc, he⟩ := D.exists_nd_separated_reduction ha ht h hx hx1 hsep
  have hs := congrArg (xQShift m) (hc m)
  simp only [map_add, map_mul, xQShift_C, qShift_X_sub_one, qShift_X] at hs
  rw [hs, he]
  simp only [map_add, map_mul, evalElementary_C]
  rw [ih Q (by lia), ih R (by lia)]

/-- The separated-contact input to the complete outer induction is discharged. -/
theorem separatedNDInductionStep (n m : ℕ) : SeparatedNDInductionStep n m := by
  intro D t x k _ ha ht h hx hx1 hsep ih
  exact D.expansion_of_nd_separated ha ht h hx hx1 hsep m (fun Q hQ => ih Q (Or.inl hQ))

/-- Assembly from an interior-overlap proof, supplied by `interiorNDInductionStep` downstream. -/
theorem Diagram.expansion_of_interior_nd_step {n m : ℕ}
    (D : Diagram n) (hinterior : InteriorNDInductionStep n m) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) :=
  D.expansion_of_remaining_nd_cases (separatedNDInductionStep n m) hinterior

end VerticalStripLLT.Circular

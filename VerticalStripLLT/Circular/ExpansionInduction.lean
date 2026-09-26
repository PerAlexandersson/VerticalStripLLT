import VerticalStripLLT.Circular.CornerReduction
import VerticalStripLLT.Circular.CornerMeasure
import VerticalStripLLT.Circular.NNElimination
import VerticalStripLLT.Circular.FullDNRecurrences

/-! Outer half-square-area and strict-rank induction, with the open ND step explicit. -/

namespace VerticalStripLLT.Circular

open Diagram

/-- The remaining ND semantic induction step, not an assumed polynomial recurrence. -/
def NDInductionStep (n m : ℕ) : Prop :=
  ∀ (D : Diagram n) (t x : ℤ),
    (∀ e : Edge D.area, IsCorner e → e ∈ D.strict) →
    D.edgeData.Admissible ∅ → D.EligibleDE t → ReverseBounce D t x →
    ¬ D.strictAt x → D.strictAt (x + 1) →
    (∀ Q : Diagram n,
      (Q.doubledArea < D.doubledArea ∨
        Q.doubledArea = D.doubledArea ∧ Q.strictRank < D.strictRank) →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) →
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)

/-- Every branch except ND is discharged by the checked actual-model reductions. -/
theorem Diagram.expansion_of_nd_induction_step {n m : ℕ} (D : Diagram n)
    (hnd : NDInductionStep n m) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  classical
  suffices aux : ∀ a r : ℕ, ∀ D : Diagram n,
      D.doubledArea = a → D.strictRank = r →
      xQShift m (D.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion D) by
    exact aux D.doubledArea D.strictRank D rfl rfl
  intro a
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro r
    induction r using Nat.strong_induction_on with
    | h r ihr =>
      intro D harea hrank
      have ih (Q : Diagram n)
          (hQ : Q.doubledArea < D.doubledArea ∨
            Q.doubledArea = D.doubledArea ∧ Q.strictRank < D.strictRank) :
          xQShift m (Q.coloringLLT m) =
            evalElementary m (shiftedOrientationExpansion Q) := by
        rcases hQ with hQ | ⟨hQa, hQr⟩
        · exact iha Q.doubledArea (by lia) Q.strictRank Q rfl rfl
        · exact ihr Q.strictRank (by lia) Q (hQa.trans harea) rfl
      by_cases hc : ∃ e : Edge D.area, IsCorner e ∧ e ∉ D.strict
      · obtain ⟨e, he, hns⟩ := hc
        have hs := ih (D.strictify e he) (Or.inl (by
          have := D.strictify_doubledArea e he hns
          lia))
        have hd := ih (D.deleteCorner e he) (Or.inl (by
          have := D.deleteCorner_doubledArea e he hns
          lia))
        rw [D.xQShift_coloringLLT_corner e he hns,
          D.shiftedOrientationExpansion_corner e he hns]
        simp only [map_add, map_mul, evalElementary_C, hs, hd]
      · push Not at hc
        by_cases ha : D.edgeData.Admissible ∅
        · by_cases hn : D.edgeData.normalEdges.Nonempty
          · obtain ⟨t, x, ht, h⟩ := D.exists_complete_reverseBounce hc ha hn
            rcases h.terminal_types with ⟨hx, hx1⟩ | ⟨hx, hx1⟩ | ⟨hx, hx1⟩
            · exact D.expansion_of_nn ht ha h hx hx1 m (fun Q hQ => ih Q (Or.inl hQ))
            · exact D.expansion_of_dn ha ht h hx hx1 m
                (fun Q hQa hQr => ih Q (Or.inr ⟨hQa, hQr⟩))
            · exact hnd D t x hc ha ht h hx hx1 ih
          · exact coloringLLT_shifted_eq_expansion_of_no_normal D
              (Finset.not_nonempty_iff_eq_empty.mp hn) m
        · exact coloringLLT_shifted_eq_expansion_of_not_admissible_empty D ha m

end VerticalStripLLT.Circular

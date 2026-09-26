import VerticalStripLLT.Circular.ExpansionInduction
import VerticalStripLLT.Circular.OneBounceNDRecurrences
import VerticalStripLLT.Circular.AliasRecurrences

/-! The separated and interior ND interfaces suffice for the full outer induction.
These are explicit hypotheses, not assertions that the obligations are proved. -/

namespace VerticalStripLLT.Circular

open Diagram

/-- The separated ND step with at least one DD contact. -/
def SeparatedNDInductionStep (n m : ℕ) : Prop :=
  ∀ (D : Diagram n) (t x : ℤ) (k : ℕ),
    (∀ e : Edge D.area, IsCorner e → e ∈ D.strict) →
    D.edgeData.Admissible ∅ → D.EligibleDE t → ReverseBounceN D t x (k + 1) →
    ¬ D.strictAt x → D.strictAt (x + 1) →
    (∀ i ≤ k + 1, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)) →
    (∀ Q : Diagram n,
      (Q.doubledArea < D.doubledArea ∨
        Q.doubledArea = D.doubledArea ∧ Q.strictRank < D.strictRank) →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) →
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)

/-- The interior-overlap ND step; the source is saturated. -/
def InteriorNDInductionStep (n m : ℕ) : Prop :=
  ∀ (D : Diagram n) (t x : ℤ) (k : ℕ),
    (∀ e : Edge D.area, IsCorner e → e ∈ D.strict) →
    D.edgeData.Admissible ∅ → D.EligibleDE t → ReverseBounceN D t x (k + 1) →
    ¬ D.strictAt x → D.strictAt (x + 1) →
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) →
    (∀ Q : Diagram n,
      (Q.doubledArea < D.doubledArea ∨
        Q.doubledArea = D.doubledArea ∧ Q.strictRank < D.strictRank) →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) →
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)

/-- Direct ND and root alias are already proved; only separation and interior overlap remain. -/
theorem ndInductionStep_of_remaining_cases {n m : ℕ}
    (hseparated : SeparatedNDInductionStep n m)
    (hinterior : InteriorNDInductionStep n m) : NDInductionStep n m := by
  classical
  intro D t x hsat ha ht h hx hx1 ih
  obtain ⟨k, hk⟩ := D.reverseBounce_to_counted h
  cases k with
  | zero =>
    exact D.expansion_of_oneBounce_nd ht hk hx hx1 m (fun Q hQ => ih Q (Or.inl hQ))
  | succ k =>
    by_cases hsep : ∀ i ≤ k + 1,
        D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)
    · exact hseparated D t x k hsat ha ht hk hx hx1 hsep ih
    · push Not at hsep
      obtain ⟨i, hi, heq⟩ := hsep
      by_cases hi0 : i = 0
      · subst i
        have halias : D.residue t = D.residue (x + 1) := by simpa using heq
        exact D.expansion_of_nd_alias ha ht h hx hx1 halias m
          (fun Q hQ _ => ih Q (Or.inl hQ))
      · exact hinterior D t x k hsat ha ht hk hx hx1
          ⟨i, by lia, hi, heq⟩ ih

/-- Conditional assembly of the full circular equality from the two named ND steps. -/
theorem Diagram.expansion_of_remaining_nd_cases {n m : ℕ}
    (hseparated : SeparatedNDInductionStep n m)
    (hinterior : InteriorNDInductionStep n m) (D : Diagram n) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) :=
  D.expansion_of_nd_induction_step (ndInductionStep_of_remaining_cases hseparated hinterior)

end VerticalStripLLT.Circular

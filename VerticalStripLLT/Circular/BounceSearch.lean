import VerticalStripLLT.Circular.BoundaryRow
import VerticalStripLLT.Circular.BounceSeedExistence
import VerticalStripLLT.Circular.StrictDepth
import Mathlib.Tactic.Linarith

/-! A finite reverse search through eligible strict rows. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

def EligibleDE (t : ℤ) : Prop :=
  D.strictAt t ∧ 2 ≤ D.area.area (D.residue t) ∧ 0 < D.eastGap t

inductive ReverseBounce (D : Diagram n) : ℤ → ℤ → Prop
  | stop (t : ℤ) (hgap : D.eastGap (D.boundary t) = 0)
      (hnot : ¬ (D.strictAt (D.boundary t) ∧
        D.strictAt (D.boundary t + 1))) :
      ReverseBounce D t (D.boundary t)
  | descend {t x : ℤ} (hgap : D.eastGap (D.boundary t) = 0)
      (hfirst : D.strictAt (D.boundary t))
      (hsecond : D.strictAt (D.boundary t + 1))
      (child : ReverseBounce D (D.boundary t) x) :
      ReverseBounce D t x

private theorem reverse_bounce_search
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    (ha : D.edgeData.Admissible ∅) {t : ℤ}
    (ht : D.strictAt t) (harea : 2 ≤ D.area.area (D.residue t)) :
    (∃ x, ReverseBounce D t x) ∨
      ∃ z x, D.EligibleDE z ∧ ReverseBounce D z x := by
  classical
  let R : Fin n → Fin n → Prop := D.edgeData.selected ∅
  let depth (u : Fin n) : ℕ := ancestorDepth R u
  suffices aux : ∀ d : ℕ, ∀ t : ℤ,
      depth (D.residue t) = d → D.strictAt t →
        2 ≤ D.area.area (D.residue t) →
        (∃ x, ReverseBounce D t x) ∨
          ∃ z x, D.EligibleDE z ∧ ReverseBounce D z x by
    exact aux (depth (D.residue t)) t rfl ht harea
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro s hdepthEq hs hsarea
    let x : ℤ := D.boundary s
    have hsx : D.edgeData.selected ∅ (D.residue x) (D.residue s) := by
      dsimp [x]
      exact D.selected_of_strictAt hs
    have hdepth : depth (D.residue x) < d := by
      rw [← hdepthEq]
      apply ancestorDepth_lt_of_transGen R ha
      exact Relation.TransGen.single hsx
    have hx2 : x + 2 ≤ s := by
      dsimp [x, Diagram.boundary]
      have ha' : (D.area.area (D.residue s) : ℤ) ≥ 2 := by
        exact_mod_cast hsarea
      lia
    have hmono : D.boundary (x + 1) ≤ x := by
      have := D.boundary_monotone (show x + 1 ≤ s by lia)
      dsimp [x] at this ⊢
      exact this
    have hgapx_nonneg : 0 ≤ D.eastGap x := D.eastGap_nonneg x
    by_cases hgapx : 0 < D.eastGap x
    · have hstepx : D.boundary x < D.boundary (x + 1) := by
        by_cases hstrict : D.strictAt x
        · unfold eastGap at hgapx
          simp [hstrict] at hgapx
          lia
        · unfold eastGap at hgapx
          simp [hstrict] at hgapx
          lia
      have hposx : 0 < D.area.area (D.residue x) := by
        have hb : D.boundary x < x := hstepx.trans_le hmono
        rw [Diagram.boundary] at hb
        lia
      have hstrictx : D.strictAt x :=
        D.strictAt_of_boundary_step hsat hposx hstepx
      have harea_x : 2 ≤ D.area.area (D.residue x) := by
        have hgap' := hgapx
        rw [eastGap, ite_eq_left hstrictx] at hgap'
        have hb : D.boundary x = x - (D.area.area (D.residue x) : ℤ) := rfl
        lia
      have helig : D.EligibleDE x := ⟨hstrictx, harea_x, hgapx⟩
      rcases ih (depth (D.residue x)) hdepth x rfl hstrictx harea_x with hdirect | hrestart
      · rcases hdirect with ⟨y, hy⟩
        exact Or.inr ⟨x, y, helig, hy⟩
      · exact Or.inr hrestart
    · by_cases hdd : D.strictAt x ∧ D.strictAt (x + 1)
      · have hzero : D.eastGap x = 0 := le_antisymm (by lia) hgapx_nonneg
        have harea_x : 2 ≤ D.area.area (D.residue x) := by
          have hs2 := D.strictAt_boundary_lt hdd.2
          have hfirst : D.boundary x + 1 = D.boundary (x + 1) := by
            unfold eastGap at hzero
            simp [hdd.1] at hzero
            lia
          have hbound : D.boundary (x + 2) ≤ x := D.boundary_monotone hx2
          have hb : D.boundary x = x - (D.area.area (D.residue x) : ℤ) := rfl
          have hadd : x + 1 + 1 = x + 2 := by ring
          rw [hadd] at hs2
          lia
        rcases ih (depth (D.residue x)) hdepth x rfl hdd.1 harea_x with hdirect | hrestart
        · rcases hdirect with ⟨y, hy⟩
          exact Or.inl ⟨y, ReverseBounce.descend hzero hdd.1 hdd.2 hy⟩
        · exact Or.inr hrestart
      · have hzero : D.eastGap (D.boundary s) = 0 := by
          exact le_antisymm (by
            dsimp [x] at hgapx
            exact not_lt.mp hgapx) (D.eastGap_nonneg _)
        exact Or.inl ⟨_, ReverseBounce.stop _ hzero hdd⟩

theorem exists_reverseBounce
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    (ha : D.edgeData.Admissible ∅) {t : ℤ}
    (ht : D.EligibleDE t) :
    ∃ z x, D.EligibleDE z ∧ ReverseBounce D z x := by
  rcases reverse_bounce_search D hsat ha ht.1 ht.2.1 with hdirect | hrestart
  · rcases hdirect with ⟨x, hx⟩
    exact ⟨t, x, ht, hx⟩
  · exact hrestart

/-- Every remaining diagram admits a complete reverse contact search, including restarts. -/
theorem exists_complete_reverseBounce
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    (ha : D.edgeData.Admissible ∅) (hn : D.edgeData.normalEdges.Nonempty) :
    ∃ z x, D.EligibleDE z ∧ ReverseBounce D z x := by
  obtain ⟨t, ht⟩ := D.exists_eligible_seed hsat ha hn
  exact D.exists_reverseBounce hsat ha ht

namespace ReverseBounce

variable {D}

theorem terminal_gap {t x : ℤ} (h : ReverseBounce D t x) :
    D.eastGap x = 0 ∧ ¬ (D.strictAt x ∧ D.strictAt (x + 1)) := by
  induction h with
  | stop _ hgap hnot => exact ⟨hgap, hnot⟩
  | descend _ _ _ _ ih => exact ih

theorem terminal_types {t x : ℤ} (h : ReverseBounce D t x) :
    (¬ D.strictAt x ∧ ¬ D.strictAt (x + 1)) ∨
      (D.strictAt x ∧ ¬ D.strictAt (x + 1)) ∨
      (¬ D.strictAt x ∧ D.strictAt (x + 1)) := by
  have := h.terminal_gap.2
  tauto

/-- The search follows actual strict edges in one fixed source diagram. -/
theorem selected_path {t x : ℤ} (h : ReverseBounce D t x) (ht : D.strictAt t) :
    Relation.TransGen (D.edgeData.selected ∅) (D.residue x) (D.residue t) := by
  induction h with
  | stop t _ _ => exact Relation.TransGen.single (D.selected_of_strictAt ht)
  | descend _ hfirst _ _ ih =>
      exact (ih hfirst).trans (Relation.TransGen.single (D.selected_of_strictAt ht))

end ReverseBounce

end Diagram
end VerticalStripLLT.Circular

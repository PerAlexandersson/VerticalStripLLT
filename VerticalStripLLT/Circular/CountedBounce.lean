import VerticalStripLLT.Circular.BounceSearch

/-! A counted version of the finite reverse bounce search. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

inductive ReverseBounceN (D : Diagram n) : ℤ → ℤ → ℕ → Prop
  | stop (t : ℤ) (hgap : D.eastGap (D.boundary t) = 0)
      (hnot : ¬ (D.strictAt (D.boundary t) ∧
        D.strictAt (D.boundary t + 1))) :
      ReverseBounceN D t (D.boundary t) 0
  | descend {t x : ℤ} {k : ℕ}
      (hgap : D.eastGap (D.boundary t) = 0)
      (hfirst : D.strictAt (D.boundary t))
      (hsecond : D.strictAt (D.boundary t + 1))
      (child : ReverseBounceN D (D.boundary t) x k) :
      ReverseBounceN D t x (k + 1)

theorem ReverseBounceN.to_reverseBounce {t x : ℤ} {k : ℕ}
    (h : ReverseBounceN D t x k) : ReverseBounce D t x := by
  induction h with
  | stop t hgap hnot => exact ReverseBounce.stop t hgap hnot
  | descend hgap hfirst hsecond child ih =>
      exact ReverseBounce.descend hgap hfirst hsecond ih

theorem reverseBounce_to_counted {t x : ℤ}
    (h : ReverseBounce D t x) : ∃ k, ReverseBounceN D t x k := by
  induction h with
  | stop t hgap hnot => exact ⟨0, ReverseBounceN.stop t hgap hnot⟩
  | descend hgap hfirst hsecond child ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, ReverseBounceN.descend hgap hfirst hsecond hk⟩

theorem reverseBounce_iff_counted {t x : ℤ} :
    ReverseBounce D t x ↔ ∃ k, ReverseBounceN D t x k := by
  constructor
  · exact reverseBounce_to_counted D
  · rintro ⟨k, hk⟩
    exact hk.to_reverseBounce

theorem ReverseBounceN.zero_iff {t x : ℤ} :
    ReverseBounceN D t x 0 ↔
      x = D.boundary t ∧ D.eastGap x = 0 ∧
        ¬ (D.strictAt x ∧ D.strictAt (x + 1)) := by
  constructor
  · intro h
    cases h with
    | stop t hgap hnot => exact ⟨rfl, hgap, hnot⟩
  · rintro ⟨rfl, hgap, hnot⟩
    exact ReverseBounceN.stop t hgap hnot

theorem ReverseBounceN.terminal_gap {t x : ℤ} {k : ℕ}
    (h : ReverseBounceN D t x k) :
    D.eastGap x = 0 ∧ ¬ (D.strictAt x ∧ D.strictAt (x + 1)) := by
  exact (h.to_reverseBounce).terminal_gap

theorem ReverseBounceN.selected_path {t x : ℤ} {k : ℕ}
    (h : ReverseBounceN D t x k) (ht : D.strictAt t) :
    Relation.TransGen (D.edgeData.selected ∅) (D.residue x) (D.residue t) := by
  exact h.to_reverseBounce.selected_path ht

theorem reverseBounceN_succ_iff {t x : ℤ} {k : ℕ} :
    ReverseBounceN D t x (k + 1) ↔
      D.eastGap (D.boundary t) = 0 ∧
      D.strictAt (D.boundary t) ∧ D.strictAt (D.boundary t + 1) ∧
      ReverseBounceN D (D.boundary t) x k := by
  constructor
  · intro h
    cases h with
    | descend hgap hfirst hsecond child =>
        exact ⟨hgap, hfirst, hsecond, child⟩
  · rintro ⟨hgap, hfirst, hsecond, child⟩
    exact ReverseBounceN.descend hgap hfirst hsecond child

end Diagram
end VerticalStripLLT.Circular

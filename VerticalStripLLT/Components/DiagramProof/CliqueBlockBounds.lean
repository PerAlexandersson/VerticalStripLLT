import VerticalStripLLT.Components.DiagramProof.CliqueBlockReplacement

/-! Interval bounds for weak reachability inside a selected clique block. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

theorem eqvGen_cliqueBlockRelation_eq_or_bounds
    {n : ℕ} {D : Diagram n} (e : Edge D.area) (θ : Orientation D)
    {x y : Fin n}
    (h : Relation.EqvGen (cliqueBlockRelation e θ) x y) :
    x = y ∨
      (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) := by
  induction h with
  | refl => exact Or.inl rfl
  | rel x y hxy => exact Or.inr ⟨hxy.1, hxy.2.1⟩
  | symm x y hxy ih =>
      rcases ih with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
  | trans x y z hxy hyz ihxy ihyz =>
      rcases ihxy with rfl | ⟨hx, hz⟩
      · exact ihyz
      · rcases ihyz with rfl | ⟨_, hz'⟩
        · exact Or.inr ⟨hx, hz⟩
        · exact Or.inr ⟨hx, hz'⟩

theorem cliqueBlockRelation_iff_of_forward
    {n : ℕ} {D : Diagram n} (hD : Forward D)
    (e : Edge D.area) (θ : Orientation D) (x y : Fin n) :
    cliqueBlockRelation e θ x y ↔
      e.tail ≤ x ∧ y ≤ e.head ∧ D.edgeData.selected θ.val x y := by
  constructor
  · rintro ⟨⟨ht, _⟩, ⟨_, hh⟩, hsel⟩
    exact ⟨ht, hh, hsel⟩
  · rintro ⟨ht, hh, hsel⟩
    have hxy := θ.selected_lt_of_forward hD hsel
    refine ⟨⟨ht, ?_⟩, ⟨?_, hh⟩, hsel⟩
    · exact hxy.le.trans hh
    · exact ht.trans hxy.le

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Circular.DNTargetPairs
import VerticalStripLLT.Circular.BoundaryRow

/-! The exact strict rows of a valid DN successor. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem strictAt_iff_exists_selected (z : ℤ) :
    D.strictAt z ↔ ∃ u, D.edgeData.selected ∅ u (D.residue z) := by
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e.tail, e, by simpa [edgeData] using he, rfl, hh⟩
  · rintro ⟨u, e, he, _, hh⟩
    exact ⟨e, by simpa [edgeData] using he, hh⟩

theorem dnSuccessor_strictAt_iff (e f : Edge D.area) (he : e ∈ D.strict)
    (hf : f ∈ D.strict) (hne : f ≠ e)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) (z : ℤ) :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).strictAt z ↔
      (D.strictAt z ∧ D.residue z ≠ e.head) ∨ D.residue z = D.area.next e.head := by
  have hef : f.head ≠ e.head := fun hh =>
    hne (D.strict_edge_eq_of_head_eq hf he hh)
  rw [strictAt_iff_exists_selected]
  change (∃ u, (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).edgeData.selected
    ∅ u (D.residue z)) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    rcases (D.dnSuccessor_selected_iff e f he hf hne heq hb hns hlen hgap
      u (D.residue z)).mp hu with ⟨hs, hse, _⟩ | ⟨_, hh⟩ | ⟨_, hh⟩
    · refine Or.inl ⟨(D.strictAt_iff_exists_selected z).mpr ⟨u, hs⟩, ?_⟩
      intro hz
      obtain ⟨s, hs, ht, hh⟩ := hs
      have hs' : s ∈ D.strict := by simpa [edgeData] using hs
      have hse' : s = e := D.strict_edge_eq_of_head_eq hs' he (hh.trans hz)
      exact hse ⟨ht.symm.trans (congrArg Edge.tail hse'), hz⟩
    · exact Or.inr hh
    · exact Or.inl ⟨⟨f, hf, hh.symm⟩, hh ▸ hef⟩
  · intro hz
    rcases hz with ⟨⟨s, hs, hh⟩, hse⟩ | hz
    · by_cases hsf : s = f
      · refine ⟨D.area.next f.tail, ?_⟩
        apply (D.dnSuccessor_selected_iff e f he hf hne heq hb hns hlen hgap _ _).mpr
        exact Or.inr (Or.inr ⟨rfl, hh.symm.trans (congrArg Edge.head hsf)⟩)
      · refine ⟨s.tail, ?_⟩
        apply (D.dnSuccessor_selected_iff e f he hf hne heq hb hns hlen hgap _ _).mpr
        refine Or.inl ⟨⟨s, by simpa [edgeData] using hs, rfl, hh⟩,
          fun h => hse h.2, ?_⟩
        intro h
        exact hsf (D.strict_edge_eq_of_head_eq hs hf (hh.trans h.2))
    · refine ⟨e.tail, ?_⟩
      apply (D.dnSuccessor_selected_iff e f he hf hne heq hb hns hlen hgap _ _).mpr
      exact Or.inr (Or.inl ⟨rfl, hz⟩)

end VerticalStripLLT.Circular.Diagram

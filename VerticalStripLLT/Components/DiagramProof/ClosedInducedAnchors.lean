import VerticalStripLLT.Components.DiagramProof.InducedAnchors

/-! Anchor restriction when the retained vertices are closed under corner successors.

A deleted initial corner need not survive. Closure under successors suffices to
preserve the chain terminal at every retained vertex.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {k n : ℕ} {D : Diagram n}
variable (F : CornerFamily D) (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
variable (hclosed : ∀ u v, F.step (ι u) v → ∃ w, ι w = v)

include hclosed

/-- Deleting predecessors leaves the terminal of each retained chain vertex unchanged. -/
theorem terminal_induced_of_closed (u : Fin (k + 1)) :
    ι ((F.induced hD ι).terminal (inducedDiagram_forward hD ι) u) =
      F.terminal hD (ι u) :=
  F.induced_terminal_eq (F.induced hD ι) hD (inducedDiagram_forward hD ι) ι
    (F.induced_step_iff hD ι) hclosed u

theorem goodEdge_induced_iff_of_closed (e : Edge (inducedDiagram hD ι).area) :
    (F.induced hD ι).GoodEdge (inducedDiagram_forward hD ι) e ↔
      F.GoodEdge hD (inducedEdge hD ι e) := by
  simp only [GoodEdge, mem_induced_edges, inducedEdge_tail, inducedEdge_head]
  apply or_congr Iff.rfl
  rw [← ι.lt_iff_lt, F.terminal_induced_of_closed hD ι hclosed,
    F.terminal_induced_of_closed hD ι hclosed]

theorem anchor_inducedRestrict_of_closed (θ : Orientation D) (hθ : F.Anchor hD θ) :
    (F.induced hD ι).Anchor (inducedDiagram_forward hD ι)
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
  constructor
  · intro e he
    apply (inducedRestrict_mem_fullSelection_iff hD ι θ e).mpr
    exact hθ.1 ((F.mem_induced_edges hD ι e).mp he)
  · intro e he
    apply (F.goodEdge_induced_iff_of_closed hD ι hclosed e).mpr
    exact hθ.2 _ ((inducedRestrict_mem_fullSelection_iff hD ι θ e).mp he)

/-- At the endpoint of a core replacement, restored exterior corners are still present. -/
theorem anchor_of_induced_replacement_of_closed (θ ζ : Orientation D) (hθ : F.Anchor hD θ)
    (α : Orientation (inducedDiagram hD ι))
    (hα : (F.induced hD ι).Anchor (inducedDiagram_forward hD ι) α)
    (hinside : ∀ u v, D.edgeData.selected ζ.val (ι u) (ι v) ↔
      (inducedDiagram hD ι).edgeData.selected α.val u v)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected ζ.val u v ↔ D.edgeData.selected θ.val u v)) :
    F.Anchor hD ζ := by
  have outside (e : Edge D.area) (hno : ¬ ∃ a b, ι a = e.tail ∧ ι b = e.head) :
      e ∈ fullSelection ζ ↔ e ∈ fullSelection θ := by
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
    exact houtside e.tail e.head hno
  have inside (e : Edge (inducedDiagram hD ι).area) :
      inducedEdge hD ι e ∈ fullSelection ζ ↔ e ∈ fullSelection α := by
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
      inducedEdge_tail, inducedEdge_head, hinside]
  constructor
  · intro e he
    by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι e).mpr hcore
      rw [← hf]
      exact (inside f).mpr (hα.1 ((F.mem_induced_edges hD ι f).mpr (hf.symm ▸ he)))
    · exact (outside e hcore).mpr (hθ.1 he)
  · intro e he
    by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι e).mpr hcore
      have hsel := (inside f).mp (hf.symm ▸ he)
      exact hf ▸ (F.goodEdge_induced_iff_of_closed hD ι hclosed f).mp (hα.2 f hsel)
    · exact hθ.2 e ((outside e hcore).mp he)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

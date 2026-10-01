import VerticalStripLLT.Components.DiagramProof.Restriction.InducedCornerFamily
import VerticalStripLLT.Components.DiagramProof.Restriction.InducedTerminals
import VerticalStripLLT.Components.DiagramProof.Restriction.InducedRestriction
import VerticalStripLLT.Components.DiagramProof.Corners.GoodEdges

/-! Terminal labels, good edges, and anchors under corner-preserving restriction. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {D : Diagram n}

theorem inducedRestrict_mem_fullSelection_iff (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (θ : Orientation D)
    (e : Edge (inducedDiagram hD ι).area) :
    e ∈ fullSelection (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ) ↔
      inducedEdge hD ι e ∈ fullSelection θ := by
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    inducedRestrict_selected, inducedEdge_tail, inducedEdge_head]

namespace CornerFamily

variable (F : CornerFamily D) (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
  (hcorners : ∀ e ∈ F.edges, ∃ u v, ι u = e.tail ∧ ι v = e.head)

include hcorners

/-- Chain terminal labels agree after embedding the retained vertices. -/
theorem terminal_induced (u : Fin (k + 1)) :
    ι ((F.induced hD ι).terminal (inducedDiagram_forward hD ι) u) =
      F.terminal hD (ι u) :=
  F.induced_terminal_eq (F.induced hD ι) hD (inducedDiagram_forward hD ι) ι
    (F.induced_step_iff hD ι) (F.induced_step_closed ι hcorners) u

/-- Good edges in the core are exactly the ambient good edges with retained endpoints. -/
theorem goodEdge_induced_iff (e : Edge (inducedDiagram hD ι).area) :
    (F.induced hD ι).GoodEdge (inducedDiagram_forward hD ι) e ↔
      F.GoodEdge hD (inducedEdge hD ι e) := by
  simp only [GoodEdge, mem_induced_edges, inducedEdge_tail, inducedEdge_head]
  apply or_congr Iff.rfl
  rw [← ι.lt_iff_lt, F.terminal_induced hD ι hcorners,
    F.terminal_induced hD ι hcorners]

/-- Restriction of an ambient anchor is an anchor for the retained core family. -/
theorem anchor_inducedRestrict (θ : Orientation D) (hθ : F.Anchor hD θ) :
    (F.induced hD ι).Anchor (inducedDiagram_forward hD ι)
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
  constructor
  · intro e he
    apply (inducedRestrict_mem_fullSelection_iff hD ι θ e).mpr
    exact hθ.1 ((F.mem_induced_edges hD ι e).mp he)
  · intro e he
    apply (F.goodEdge_induced_iff hD ι hcorners e).mpr
    exact hθ.2 _ ((inducedRestrict_mem_fullSelection_iff hD ι θ e).mp he)

/-- Replacing the core of an anchor by a core anchor preserves the ambient anchor
when every retained corner survives and every exterior edge is restored. -/
theorem anchor_of_induced_replacement (θ ζ : Orientation D) (hθ : F.Anchor hD θ)
    (α : Orientation (inducedDiagram hD ι))
    (hα : (F.induced hD ι).Anchor (inducedDiagram_forward hD ι) α)
    (hinside : ∀ u v, D.edgeData.selected ζ.val (ι u) (ι v) ↔
      (inducedDiagram hD ι).edgeData.selected α.val u v)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected ζ.val u v ↔ D.edgeData.selected θ.val u v)) :
    F.Anchor hD ζ := by
  constructor
  · intro e he
    obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι e).mpr (hcorners e he)
    have hsel := (mem_fullSelection_iff_selected α f).mp
      (hα.1 ((F.mem_induced_edges hD ι f).mpr (hf.symm ▸ he)))
    have hz := (hinside f.tail f.head).mpr hsel
    apply (mem_fullSelection_iff_selected ζ e).mpr
    simpa only [← hf, inducedEdge_tail, inducedEdge_head] using hz
  · intro e he
    classical
    by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι e).mpr hcore
      have hz := (mem_fullSelection_iff_selected ζ e).mp he
      have hsel : (inducedDiagram hD ι).edgeData.selected α.val f.tail f.head := by
        apply (hinside f.tail f.head).mp
        simpa only [← hf, inducedEdge_tail, inducedEdge_head] using hz
      have hgood := (F.goodEdge_induced_iff hD ι hcorners f).mp
        (hα.2 f ((mem_fullSelection_iff_selected α f).mpr hsel))
      exact hf ▸ hgood
    · apply hθ.2 e
      apply (mem_fullSelection_iff_selected θ e).mpr
      exact (houtside e.tail e.head hcore).mp ((mem_fullSelection_iff_selected ζ e).mp he)

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof

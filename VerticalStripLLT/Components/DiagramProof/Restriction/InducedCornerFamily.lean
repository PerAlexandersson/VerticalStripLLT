import VerticalStripLLT.Components.DiagramProof.Restriction.InducedDecorations

/-! Retained corner families under increasing restriction. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n} (F : CornerFamily D)
  (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)

theorem ext_edges {F G : CornerFamily D} (h : F.edges = G.edges) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Retain precisely the family edges whose two endpoints survive. -/
def induced : CornerFamily (inducedDiagram hD ι) where
  edges := Finset.univ.filter fun e => inducedEdge hD ι e ∈ F.edges
  corner := by
    intro e he
    exact isCorner_of_inducedEdge_isCorner hD ι e (F.corner _ (Finset.mem_filter.mp he).2)
  contains_strict := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      F.contains_strict ((mem_inducedDiagram_strict hD ι e).mp he)⟩

@[simp]
theorem mem_induced_edges (e : Edge (inducedDiagram hD ι).area) :
    e ∈ (F.induced hD ι).edges ↔ inducedEdge hD ι e ∈ F.edges := by
  change e ∈ Finset.univ.filter (fun f => inducedEdge hD ι f ∈ F.edges) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

/-- The retained chain relation is the induced ambient chain relation. -/
theorem induced_step_iff (u v : Fin (k + 1)) :
    (F.induced hD ι).step u v ↔ F.step (ι u) (ι v) := by
  rw [(F.induced hD ι).step_iff, F.step_iff]
  constructor
  · rintro ⟨e, he, rfl, rfl⟩
    exact ⟨inducedEdge hD ι e, (F.mem_induced_edges hD ι e).mp he,
      inducedEdge_tail hD ι e, inducedEdge_head hD ι e⟩
  · rintro ⟨f, hf, ht, hh⟩
    obtain ⟨e, he⟩ := (mem_range_inducedEdge_iff hD ι f).mpr
      ⟨u, v, ht.symm, hh.symm⟩
    refine ⟨e, (F.mem_induced_edges hD ι e).mpr (he.symm ▸ hf), ?_, ?_⟩
    · apply ι.injective
      rw [← inducedEdge_tail, he, ht]
    · apply ι.injective
      rw [← inducedEdge_head, he, hh]

/-- Keeping the endpoints of every retained corner closes the image under chain steps. -/
theorem induced_step_closed
    (hcorners : ∀ e ∈ F.edges, ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (u : Fin (k + 1)) (v : Fin n) (h : F.step (ι u) v) : ∃ w, ι w = v := by
  obtain ⟨e, he, _, hh⟩ := (F.step_iff _ _).mp h
  obtain ⟨_, w, _, hw⟩ := hcorners e he
  exact ⟨w, hw.trans hh⟩

/-- When every maximal corner survives, the restricted full family is the full core family. -/
theorem induced_allCorners
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head) :
    (allCorners D).induced hD ι = allCorners (inducedDiagram hD ι) := by
  apply ext_edges
  ext e
  rw [mem_induced_edges]
  change (inducedEdge hD ι e ∈ Finset.univ.filter IsCorner) ↔
    e ∈ Finset.univ.filter IsCorner
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inducedEdge_isCorner_iff hD ι hcorners e

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

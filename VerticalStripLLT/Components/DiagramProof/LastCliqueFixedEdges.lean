import VerticalStripLLT.Components.DiagramProof.LastCliqueTreePath
import VerticalStripLLT.Components.DiagramProof.SelectedCoreTree

/-! The fixed selection displayed as the retained tree with the omitted terminal leaves. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Lift the core tree edges and add the omitted vertices' terminal-star edges. -/
def lastCliqueFixedEdges (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (c : Fin n) (g : Edge D.area) (T : SimpleGraph (Fin (k + 1))) :
    Finset (Edge D.area) :=
  (Finset.univ.filter (fun e : Edge (inducedDiagram hD ι).area =>
    T.Adj e.tail e.head)).map (inducedEdgeEmbedding hD ι) ∪
    Finset.univ.filter (fun e : Edge D.area => c < e.tail ∧ e.head = g.head)

theorem inducedEdge_mem_lastCliqueFixedEdges (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (T : SimpleGraph (Fin (k + 1))) (e : Edge (inducedDiagram hD ι).area)
    (he : T.Adj e.tail e.head) :
    inducedEdge hD ι e ∈ lastCliqueFixedEdges hD ι c g T := by
  apply Finset.mem_union_left
  exact Finset.mem_map.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

/-- Restriction of the displayed fixed selection contains no added leaf edge. -/
theorem inducedEdge_mem_lastCliqueFixedEdges_iff (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (T : SimpleGraph (Fin (k + 1))) (e : Edge (inducedDiagram hD ι).area) :
    inducedEdge hD ι e ∈ lastCliqueFixedEdges hD ι c g T ↔ T.Adj e.tail e.head := by
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
      have hfe' : f = e := (inducedEdgeEmbedding hD ι).injective hfe
      subst f
      exact (Finset.mem_filter.mp hf).2
    · obtain ⟨hc, hh⟩ := (Finset.mem_filter.mp he).2
      rw [inducedEdge_tail] at hc
      have ht : ι e.tail = g.head := ((himage (ι e.tail)).mp ⟨e.tail, rfl⟩).resolve_left
        (not_le_of_gt hc)
      have hlt := hD (inducedEdge hD ι e)
      rw [inducedEdge_tail, ht, hh] at hlt
      exact (lt_irrefl _ hlt).elim
  · exact inducedEdge_mem_lastCliqueFixedEdges hD ι c g T e

/-- The path endpoint selecting the core tree and full star contains the fixed selection. -/
theorem lastCliqueFixedEdges_subset_selection (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area) (hgc : g.tail ≤ c)
    (T : SimpleGraph (Fin (k + 1))) (θ : Orientation D)
    (hcore : ∀ e : Edge (inducedDiagram hD ι).area, T.Adj e.tail e.head →
      D.edgeData.selected θ.val (ι e.tail) (ι e.head))
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head) :
    lastCliqueFixedEdges hD ι c g T ⊆ fullSelection θ := by
  intro e he
  apply (mem_fullSelection_iff_selected θ e).mpr
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    change D.edgeData.selected θ.val (inducedEdge hD ι f).tail (inducedEdge hD ι f).head
    rw [inducedEdge_tail, inducedEdge_head]
    exact hcore f (Finset.mem_filter.mp hf).2
  · obtain ⟨hc, hh⟩ := (Finset.mem_filter.mp he).2
    rw [hh]
    exact hstar _ (hgc.trans hc.le) (by simpa only [← hh] using hD e)

/-- Any orientation containing the fixed selection has connected core restriction. -/
theorem lastCliqueFixedEdges_connected_core (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.Connected)
    (hTG : T ≤ edgeSetGraph (Finset.univ : Finset (Edge (inducedDiagram hD ι).area)))
    (θ : Orientation D) (hA : lastCliqueFixedEdges hD ι c g T ⊆ fullSelection θ) :
    SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
  apply selectedConnected_inducedRestrict_of_selected_tree (inducedDiagram_forward hD ι) ι
    (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) T hT hTG θ
  intro e he
  have hsel := (mem_fullSelection_iff_selected θ (inducedEdge hD ι e)).mp
    (hA (inducedEdge_mem_lastCliqueFixedEdges hD ι c g T e he))
  simpa only [inducedEdge_tail, inducedEdge_head] using hsel

/-- Every retained corner belongs to the fixed selection. -/
theorem allCorners_subset_lastCliqueFixedEdges (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (T : SimpleGraph (Fin (k + 1)))
    (hFT : edgeSetGraph (allCorners (inducedDiagram hD ι)).edges ≤ T) :
    (allCorners D).edges ⊆ lastCliqueFixedEdges hD ι c g T := by
  intro e he
  have hc := (allCorners D).corner e he
  obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι e).mpr (hcorners e hc)
  have hfc : IsCorner f := isCorner_of_inducedEdge_isCorner hD ι f (hf.symm ▸ hc)
  rw [← hf]
  apply inducedEdge_mem_lastCliqueFixedEdges
  exact hFT ((edgeSetGraph_adj_iff_mem (inducedDiagram_forward hD ι) _ f).mpr
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc⟩))

/-- The lifted core star and omitted leaves together give the full terminal star. -/
theorem lastCliqueFixedEdges_star (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (T : SimpleGraph (Fin (k + 1)))
    (hstar : ∀ u v, g.tail ≤ ι u → ι u < g.head → ι v = g.head → T.Adj u v)
    (v : Fin n) (hav : g.tail ≤ v) (hve : v < g.head) :
    (edgeSetGraph (lastCliqueFixedEdges hD ι c g T)).Adj v g.head := by
  obtain ⟨e, het, heh⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head g (hD g)) hav hve le_rfl
  have heA : e ∈ lastCliqueFixedEdges hD ι c g T := by
    by_cases hvc : v ≤ c
    · obtain ⟨u, hu⟩ := (himage v).mpr (Or.inl hvc)
      obtain ⟨j, hj⟩ := (himage g.head).mpr (Or.inr rfl)
      obtain ⟨f, hft, hfh⟩ := (inducedDiagram_naturalEdge_iff hD ι u j).mpr
        ⟨e, het.trans hu.symm, heh.trans hj.symm⟩
      have hfe : inducedEdge hD ι f = e := by
        apply D.endpointEmbedding.injective
        exact Prod.ext ((inducedEdge_tail hD ι f).trans ((congrArg ι hft).trans
          (hu.trans het.symm))) ((inducedEdge_head hD ι f).trans ((congrArg ι hfh).trans
          (hj.trans heh.symm)))
      rw [← hfe]
      apply inducedEdge_mem_lastCliqueFixedEdges
      rw [hft, hfh]
      exact hstar u j (hu.symm ▸ hav) (hu.symm ▸ hve) hj
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa only [het] using lt_of_not_ge hvc, heh⟩
  simpa only [het, heh] using (edgeSetGraph_adj_iff_mem hD _ e).mpr heA

end

end VerticalStripLLT.Circular.DiagramProof

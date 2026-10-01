import VerticalStripLLT.Components.DiagramProof.LastCliqueFixedEdges
import VerticalStripLLT.Components.DiagramProof.TreeOmissions

/-! A crossing pair forces omission of the shared position from the fixed tree. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

theorem crossing_shared_not_mem_lastCliqueFixedEdges
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (f g p : Edge D.area) (hf : f ∈ (allCorners D).edges)
    (hg : g ∈ (allCorners D).edges)
    (hfp : p.tail = f.tail) (hpg : p.head = g.tail)
    (hcross : f.tail < g.tail ∧ g.tail < f.head ∧ f.head < g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ f.head ∨ z = g.head)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsAcyclic)
    (hFT : edgeSetGraph (allCorners (inducedDiagram hD ι)).edges ≤ T)
    (hstar : ∀ u v, g.tail ≤ ι u → ι u < g.head → ι v = g.head → T.Adj u v) :
    p ∉ lastCliqueFixedEdges hD ι f.head g T := by
  have hcorner (e : Edge D.area) (he : e ∈ (allCorners D).edges) :
      IsCorner e := (allCorners D).corner e he
  have himage_of_le {z : Fin n} (hz : z ≤ f.head) : ∃ w, ι w = z :=
    (himage z).mpr (Or.inl hz)
  have hcore (e : Edge D.area) (he : e ∈ (allCorners D).edges)
      (u v : Fin (k + 1)) (ht : ι u = e.tail) (hh : ι v = e.head) :
      ∃ e' : Edge (inducedDiagram hD ι).area,
        e'.tail = u ∧ e'.head = v ∧
        IsCorner e' := by
    obtain ⟨e', hte, hhe⟩ := (inducedDiagram_naturalEdge_iff hD ι
      u v).mpr ⟨e, ht.symm, hh.symm⟩
    have heq : inducedEdge hD ι e' = e := by
      apply D.endpointEmbedding.injective
      exact Prod.ext ((inducedEdge_tail hD ι e').trans
        ((congrArg ι hte).trans ht))
        ((inducedEdge_head hD ι e').trans
          ((congrArg ι hhe).trans hh))
    refine ⟨e', hte, hhe, ?_⟩
    exact isCorner_of_inducedEdge_isCorner hD ι e' (heq.symm ▸ hcorner e he)
  obtain ⟨ub, hub⟩ := himage_of_le (hD f).le
  obtain ⟨uc, huc⟩ := himage_of_le le_rfl
  obtain ⟨ua, hua⟩ := himage_of_le hcross.2.1.le
  obtain ⟨ue, hue⟩ := (himage g.head).mpr (Or.inr rfl)
  obtain ⟨fc, hfc_tail, hfc_head, hfc_corner⟩ :=
    hcore f hf ub uc hub huc
  obtain ⟨gc, hgc_tail, hgc_head, hgc_corner⟩ :=
    hcore g hg ua ue hua hue
  have hfcT : T.Adj fc.tail fc.head :=
    hFT ((edgeSetGraph_adj_iff_mem (inducedDiagram_forward hD ι) _ fc).mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc_corner⟩))
  have hgcT : T.Adj gc.tail gc.head :=
    hFT ((edgeSetGraph_adj_iff_mem (inducedDiagram_forward hD ι) _ gc).mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgc_corner⟩))
  obtain ⟨up, hpu_tail, hpu_head⟩ :=
    (inducedDiagram_naturalEdge_iff hD ι ub ua).mpr
      ⟨p, hfp.trans hub.symm, hpg.trans hua.symm⟩
  have huppe : inducedEdge hD ι up = p := by
    apply D.endpointEmbedding.injective
    exact Prod.ext ((inducedEdge_tail hD ι up).trans
      ((congrArg ι hpu_tail).trans (hub.trans hfp.symm)))
      ((inducedEdge_head hD ι up).trans
        ((congrArg ι hpu_head).trans (hua.trans hpg.symm)))
  intro hp
  have hpT : T.Adj up.tail up.head := by
    apply (inducedEdge_mem_lastCliqueFixedEdges_iff hD ι f.head g himage T up).mp
    simpa only [huppe] using hp
  have hba : ub < ua := by
    apply ι.lt_iff_lt.mp
    simpa only [hub, hua] using hcross.1
  have hac : ua < uc := by
    apply ι.lt_iff_lt.mp
    simpa only [hua, huc] using hcross.2.1
  have hce : uc < ue := by
    apply ι.lt_iff_lt.mp
    simpa only [huc, hue] using hcross.2.2
  have hceT : T.Adj uc ue := by
    apply hstar uc ue
    · simpa only [huc] using hcross.2.1.le
    · simpa only [huc] using hcross.2.2
    · exact hue
  exact SimpleGraph.not_adj_of_three_edge_path hT hba hac hce
    (by simpa only [hfc_tail, hfc_head] using hfcT)
    (by simpa only [hfc_head, hue] using hceT)
    (by simpa only [hgc_tail, hgc_head] using hgcT) (by simpa only [hpu_tail, hpu_head] using hpT)

end

end VerticalStripLLT.Circular.DiagramProof

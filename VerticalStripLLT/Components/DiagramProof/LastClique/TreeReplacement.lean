import VerticalStripLLT.Components.DiagramProof.LastClique.TreeAnchors
import VerticalStripLLT.Components.DiagramProof.LastClique.Tree
import VerticalStripLLT.Components.DiagramProof.LastClique.AnchorReplacement

/-! Reaching a prescribed good core tree using smaller-core uniqueness and diagram sweeps. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- The retained core has a good tree containing its corners and the displayed last star. -/
theorem exists_lastClique_core_tree
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (θ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hconnected : SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ)) :
    ∃ T : SimpleGraph (Fin (k + 1)), T.IsTree ∧
      edgeSetGraph (allCorners (inducedDiagram hD ι)).edges ≤ T ∧
      T ≤ edgeSetGraph ((allCorners (inducedDiagram hD ι)).goodEdges
        (inducedDiagram_forward hD ι)) ∧
      ∀ u v, g.tail ≤ ι u → ι u < g.head → ι v = g.head → T.Adj u v := by
  let E := inducedDiagram hD ι
  let hE := inducedDiagram_forward hD ι
  let F := allCorners E
  let θcore := inducedRestrict hE ι (inducedDiagram_naturalEdge_iff hD ι)
    (inducedDiagram_strictEndpoint_iff hD ι) θ
  have hcore : F.Anchor hE θcore := by
    have h := (allCorners D).anchor_inducedRestrict hD ι
      (fun e he => hcorners e ((allCorners D).corner e he)) θ hθ
    simpa only [CornerFamily.induced_allCorners hD ι hcorners] using h
  obtain ⟨f, hf⟩ := (mem_range_inducedEdge_iff hD ι g).mpr (hcorners g hg)
  have hft : ι f.tail = g.tail :=
    (inducedEdge_tail hD ι f).symm.trans (congrArg Edge.tail hf)
  have hfh : ι f.head = g.head :=
    (inducedEdge_head hD ι f).symm.trans (congrArg Edge.head hf)
  have hfc : IsCorner f := isCorner_of_inducedEdge_isCorner hD ι f (hf.symm ▸ hg)
  have hflast : ∀ v : Fin (k + 1), v ≤ f.head := by
    intro v
    apply ι.le_iff_le.mp
    rw [hfh]
    exact hlast _
  obtain ⟨T, hFT, hTG, hT, hstar⟩ :=
    F.exists_last_clique_tree hE f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc⟩)
      hflast θcore hcore hconnected
  refine ⟨T, hT, hFT, hTG, ?_⟩
  intro u v hau hue hve
  have hv : v = f.head := ι.injective (hve.trans hfh.symm)
  subst v
  exact hstar u (ι.le_iff_le.mp (hft.symm ▸ hau))
    (ι.lt_iff_lt.mp (hfh.symm ▸ hue))

/-- A fixed good tree can be selected in the core with the exact ambient exterior restored.
The path hypothesis is uniqueness in the smaller core, not in the ambient diagram. -/
theorem exists_lastClique_tree_replacement
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hgc : g.tail < c) (hcg : c < g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree)
    (hFT : edgeSetGraph (allCorners (inducedDiagram hD ι)).edges ≤ T)
    (hTG : T ≤ edgeSetGraph ((allCorners (inducedDiagram hD ι)).goodEdges
      (inducedDiagram_forward hD ι)))
    (θ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hconnected : SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ)) :
    ∃ ζ : Orientation D, Relation.ReflTransGen (Flip D) θ ζ ∧
      (allCorners D).Anchor hD ζ ∧
      (∀ e : Edge (inducedDiagram hD ι).area, T.Adj e.tail e.head →
        D.edgeData.selected ζ.val (ι e.tail) (ι e.head)) ∧
      (∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
        (D.edgeData.selected ζ.val u v ↔ D.edgeData.selected θ.val u v)) := by
  let E := inducedDiagram hD ι
  let F := allCorners E
  let hE := inducedDiagram_forward hD ι
  let θcore := inducedRestrict hE ι (inducedDiagram_naturalEdge_iff hD ι)
    (inducedDiagram_strictEndpoint_iff hD ι) θ
  have hcore : F.Anchor hE θcore := by
    have h := (allCorners D).anchor_inducedRestrict hD ι
      (fun e he => hcorners e ((allCorners D).corner e he)) θ hθ
    simpa only [CornerFamily.induced_allCorners hD ι hcorners] using h
  obtain ⟨α, hα, hcα, htα, hTα⟩ :=
    F.exists_tree_anchor_replacement hE θcore hcore hconnected T hT hFT hTG
  have hp : Relation.ReflTransGen (Flip E) θcore α :=
    hunique θcore α (F.commonCover_of_anchor hE hcore) (F.commonCover_of_anchor hE hα)
      hconnected hcα htα.symm
  obtain ⟨ζ, hpath, hζ, hinside, houtside⟩ :=
    exists_lastClique_anchor_replacement_preserving_anchor hD ι c g hg hlast hgc hcg
      himage hcorners θ hθ α hα hp
  refine ⟨ζ, hpath, hζ, ?_, houtside⟩
  intro e he
  apply (hinside e.tail e.head).mpr
  apply (mem_fullSelection_iff_selected α e).mp
  exact (edgeSetGraph_adj_iff_mem hE (fullSelection α) e).mp (hTα he)

end

end VerticalStripLLT.Circular.DiagramProof

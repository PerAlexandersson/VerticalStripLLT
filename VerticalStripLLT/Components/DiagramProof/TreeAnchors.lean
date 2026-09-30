import VerticalStripLLT.Components.DiagramProof.AnchorSizes

/-! Connected anchors containing a prescribed good spanning tree. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

theorem exists_tree_anchor_replacement (θ : Orientation D)
    (hθ : F.Anchor hD θ) (hconnected : SelectedConnected θ)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (hFT : edgeSetGraph F.edges ≤ T)
    (hTG : T ≤ edgeSetGraph (F.goodEdges hD)) :
    ∃ α : Orientation D, F.Anchor hD α ∧ SelectedConnected α ∧
      totalSelected α = totalSelected θ ∧
      T ≤ edgeSetGraph (fullSelection α) := by
  let : Nonempty (Fin n) := hT.connected.nonempty
  have hθgraph : (edgeSetGraph (fullSelection θ)).Connected := by
    refine ⟨(edgeSetGraph_fullSelection_preconnected_iff θ).mpr hconnected⟩
  have hlower : Fintype.card (Fin n) ≤ totalSelected θ + 1 := by
    have hcard := hθgraph.card_vert_le_card_edgeSet_add_one
    rw [edgeSetGraph_card hD] at hcard
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, totalSelected] using hcard
  have hupper : totalSelected θ ≤ Nat.card (edgeSetGraph (F.goodEdges hD)).edgeSet := by
    have hsub : fullSelection θ ⊆ F.goodEdges hD :=
      ((F.anchor_iff_subsets hD θ).mp hθ).2
    have hcard : totalSelected θ ≤ (F.goodEdges hD).card := by
      exact Finset.card_le_card hsub
    simpa only [edgeSetGraph_card hD] using hcard
  have hG : (edgeSetGraph (F.goodEdges hD)).Connected := hT.connected.mono hTG
  obtain ⟨H, hTH, hHG, hH, hcard⟩ := exists_connected_extension_card
    (edgeSetGraph (F.goodEdges hD)) T hG hTG hT.isAcyclic
    (totalSelected θ) hlower hupper
  obtain ⟨α, hα, hgraph⟩ := F.exists_anchor_of_graph hD H
    (hFT.trans hTH) hHG
  refine ⟨α, hα, ?_, ?_, ?_⟩
  · apply (edgeSetGraph_fullSelection_preconnected_iff α).mp
    rw [hgraph]
    exact hH.preconnected
  · rw [totalSelected, ← edgeSetGraph_card hD, hgraph, hcard]
  · rw [hgraph]
    exact hTH

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

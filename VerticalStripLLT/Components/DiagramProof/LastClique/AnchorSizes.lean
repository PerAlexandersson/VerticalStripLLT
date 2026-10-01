import VerticalStripLLT.Components.DiagramProof.Foundation.EdgeSetGraph
import VerticalStripLLT.Components.DiagramProof.Corners.CornerForest
import VerticalStripLLT.Components.DiagramProof.Corners.GoodEdgeConnectivity
import VerticalStripLLT.Components.DiagramProof.LastClique.ForestExtension
import VerticalStripLLT.Components.DiagramProof.Preparation.HassePaths

/-! Connected anchors exist at every feasible size of the full good-edge diagram. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {n : ℕ} {D : Diagram n}

theorem edgeSetGraph_fullSelection_preconnected_iff (θ : Orientation D) :
    (edgeSetGraph (fullSelection θ)).Preconnected ↔ SelectedConnected θ := by
  constructor
  · intro h u v
    exact (eqvGen_iff_fromRel_reachable u v).mpr (h u v)
  · intro h u v
    exact (eqvGen_iff_fromRel_reachable u v).mp (h u v)

namespace CornerFamily

variable (F : CornerFamily D) (hforward : Forward D)

theorem corners_subset_goodEdges : F.edges ⊆ F.goodEdges hforward := by
  intro e he
  exact (F.mem_goodEdges hforward e).mpr (Or.inl he)

include hforward in
theorem edgeSetGraph_corners_isAcyclic : (edgeSetGraph F.edges).IsAcyclic := by
  have heq : edgeSetGraph F.edges = SimpleGraph.fromRel F.step := by
    apply congrArg SimpleGraph.fromRel
    funext u v
    exact propext (F.step_iff u v).symm
  rw [heq]
  exact F.stepGraph_isAcyclic hforward

/-- The full good-edge graph has all the weak connections of the natural diagram. -/
theorem goodEdgeGraph_preconnected_iff :
    (edgeSetGraph (F.goodEdges hforward)).Preconnected ↔
      ∀ u v, Relation.EqvGen (naturalRel D) u v := by
  constructor
  · intro h u v
    exact (F.eqvGen_goodEdgeRelation_iff_eqvGen_naturalRel hforward u v).mp
      ((eqvGen_iff_fromRel_reachable u v).mpr (h u v))
  · intro h u v
    exact (eqvGen_iff_fromRel_reachable u v).mp
      ((F.eqvGen_goodEdgeRelation_iff_eqvGen_naturalRel hforward u v).mpr (h u v))

/-- Every spanning subgraph between the corner forest and the good-edge graph
is the exact full-selection graph of an actual anchor. -/
theorem exists_anchor_of_graph (H : SimpleGraph (Fin n))
    (hCH : edgeSetGraph F.edges ≤ H) (hHG : H ≤ edgeSetGraph (F.goodEdges hforward)) :
    ∃ θ : Orientation D, F.Anchor hforward θ ∧ edgeSetGraph (fullSelection θ) = H := by
  let A := edgeSetGraphSub (F.goodEdges hforward) H
  have hCA : F.edges ⊆ A := by
    intro e he
    exact Finset.mem_filter.mpr ⟨F.corners_subset_goodEdges hforward he,
      hCH ((edgeSetGraph_adj_iff_mem hforward F.edges e).mpr he)⟩
  have hAG := edgeSetGraphSub_subset (F.goodEdges hforward) H
  refine ⟨ofFullSelection hforward A (F.contains_strict.trans hCA),
    F.anchor_ofFullSelection hforward A hCA hAG, ?_⟩
  rw [fullSelection_ofFullSelection]
  exact edgeSetGraphSub_eq_of_le _ _ hHG

/-- Every feasible total selected size has a connected simultaneous-cover anchor. -/
theorem exists_connected_anchor_card (hn : 0 < n)
    (hconnected : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (k : ℕ) (hlower : n ≤ k + 1) (hupper : k ≤ (F.goodEdges hforward).card) :
    ∃ θ : Orientation D, F.Anchor hforward θ ∧ SelectedConnected θ ∧ totalSelected θ = k := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hG : (edgeSetGraph (F.goodEdges hforward)).Connected :=
    ⟨(F.goodEdgeGraph_preconnected_iff hforward).mpr hconnected⟩
  obtain ⟨H, hCH, hHG, hH, hcard⟩ := exists_connected_extension_card
    (edgeSetGraph (F.goodEdges hforward)) (edgeSetGraph F.edges) hG
    (edgeSetGraph_mono (F.corners_subset_goodEdges hforward))
    (F.edgeSetGraph_corners_isAcyclic hforward) k (by simpa using hlower)
    (by simpa only [edgeSetGraph_card hforward] using hupper)
  obtain ⟨θ, hθ, hgraph⟩ := F.exists_anchor_of_graph hforward H hCH hHG
  refine ⟨θ, hθ, (edgeSetGraph_fullSelection_preconnected_iff θ).mp ?_, ?_⟩
  · rw [hgraph]
    exact hH.preconnected
  · rw [totalSelected, ← edgeSetGraph_card hforward, hgraph, hcard]

/-- A removable non-corner edge can be omitted at every feasible size below the full size. -/
theorem exists_connected_anchor_card_avoiding (d : Edge D.area)
    (hdG : d ∈ F.goodEdges hforward) (hdF : d ∉ F.edges)
    (hconnected : ((edgeSetGraph (F.goodEdges hforward)).deleteEdges
      {s(d.tail, d.head)}).Connected)
    (k : ℕ) (hlower : n ≤ k + 1) (hupper : k + 1 ≤ (F.goodEdges hforward).card) :
    ∃ θ : Orientation D, F.Anchor hforward θ ∧ SelectedConnected θ ∧
      totalSelected θ = k ∧ d ∉ fullSelection θ := by
  obtain ⟨H, hCH, hHG, hH, hcard, hdH⟩ := exists_connected_extension_card_avoiding
    (edgeSetGraph (F.goodEdges hforward)) (edgeSetGraph F.edges)
    s(d.tail, d.head) hconnected
    (edgeSetGraph_mono (F.corners_subset_goodEdges hforward))
    (F.edgeSetGraph_corners_isAcyclic hforward)
    ((edgeSetGraph_adj_iff_mem hforward _ d).mpr hdG)
    (fun hd => hdF ((edgeSetGraph_adj_iff_mem hforward _ d).mp hd))
    k (by simpa using hlower)
    (by simpa only [edgeSetGraph_card hforward] using hupper)
  obtain ⟨θ, hθ, hgraph⟩ := F.exists_anchor_of_graph hforward H hCH hHG
  refine ⟨θ, hθ, (edgeSetGraph_fullSelection_preconnected_iff θ).mp ?_, ?_, ?_⟩
  · rw [hgraph]
    exact hH.preconnected
  · rw [totalSelected, ← edgeSetGraph_card hforward, hgraph, hcard]
  · intro hd
    apply hdH
    have hadj := (edgeSetGraph_adj_iff_mem hforward (fullSelection θ) d).mpr hd
    rw [hgraph] at hadj
    exact hadj

/-- The possible total sizes of connected anchors form the full feasible interval. -/
theorem exists_connected_anchor_card_iff (hn : 0 < n)
    (hconnected : ∀ u v, Relation.EqvGen (naturalRel D) u v) (k : ℕ) :
    (∃ θ : Orientation D, F.Anchor hforward θ ∧ SelectedConnected θ ∧
      totalSelected θ = k) ↔ n ≤ k + 1 ∧ k ≤ (F.goodEdges hforward).card := by
  constructor
  · rintro ⟨θ, hθ, hc, rfl⟩
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG : (edgeSetGraph (fullSelection θ)).Connected :=
      ⟨(edgeSetGraph_fullSelection_preconnected_iff θ).mpr hc⟩
    refine ⟨?_, Finset.card_le_card ((F.anchor_iff_subsets hforward θ).mp hθ).2⟩
    have hcard := hG.card_vert_le_card_edgeSet_add_one
    rw [edgeSetGraph_card hforward, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    exact hcard
  · rintro ⟨hlower, hupper⟩
    exact F.exists_connected_anchor_card hforward hn hconnected k hlower hupper

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof

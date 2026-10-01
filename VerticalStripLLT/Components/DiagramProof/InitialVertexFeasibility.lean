import VerticalStripLLT.Components.DiagramProof.AnchorSizes
import VerticalStripLLT.Components.DiagramProof.EdgeSetGraph

/-! Cardinality bounds for connected orientations and deleted good-edge graphs. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

theorem connected_selected_card_lower_bound {n : ℕ} {D : Diagram n}
    (hD : Forward D) (hn : 0 < n) (θ : Orientation D)
    (hconn : SelectedConnected θ) :
    n ≤ totalSelected θ + 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hG : (edgeSetGraph (fullSelection θ)).Connected :=
    ⟨(edgeSetGraph_fullSelection_preconnected_iff θ).mpr hconn⟩
  have hcard := hG.card_vert_le_card_edgeSet_add_one
  rw [edgeSetGraph_card hD, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  exact hcard

namespace CornerFamily

theorem goodEdges_card_lower_bound_of_delete_connected
    {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)
    (d : Edge D.area) (hd : d ∈ F.goodEdges hD)
    (hconnected :
      ((edgeSetGraph (F.goodEdges hD)).deleteEdges {s(d.tail, d.head)}).Connected) :
    n ≤ (F.goodEdges hD).card := by
  have hcard := hconnected.card_vert_le_card_edgeSet_add_one
  rw [← edgeSetGraph_erase hD, edgeSetGraph_card hD, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hcard
  simpa only [Finset.card_erase_add_one hd] using hcard

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof

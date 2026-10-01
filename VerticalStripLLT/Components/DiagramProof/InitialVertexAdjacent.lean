import VerticalStripLLT.Components.DiagramProof.InitialVertexExtension
import VerticalStripLLT.Components.DiagramProof.InitialVertexExchange
import VerticalStripLLT.Components.DiagramProof.AnchorSizes
import VerticalStripLLT.Components.DiagramProof.ParallelMoves

/-! Adjacent choices of initial extra edges are joined by the written crossing slide.

We first choose a same-size connected core omitting the matching edge. The
smaller-core path lifts with the initial row fixed; one crossing slide then
removes the chosen initial edge and inserts its matching core edge.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {k : ℕ} {D : Diagram (k + 2)}

/-- With the matching edge removable and one free core position, an initial extra
can be deleted by an actual path while the selected core stays connected at the endpoint. -/
theorem exists_initialVertex_adjacent (F : CornerFamily D) (hD : Forward D)
    (hunique : ∀ α β : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))),
      (F.induced hD (Fin.succOrderEmb (k + 1))).CommonCover α →
      (F.induced hD (Fin.succOrderEmb (k + 1))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) α β)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hc : SelectedConnected (initialVertexRestrict hD θ))
    (e : Edge D.area) (het : e.tail = 0) (he : e ∈ fullSelection θ)
    (hegood : F.terminal hD e.tail < F.terminal hD e.head)
    (d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area)
    (hlink : F.CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d))
    (hdG : d ∈ (F.induced hD (Fin.succOrderEmb (k + 1))).goodEdges
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))
    (hdF : d ∉ (F.induced hD (Fin.succOrderEmb (k + 1))).edges)
    (hrem : ((edgeSetGraph ((F.induced hD (Fin.succOrderEmb (k + 1))).goodEdges
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
        {s(d.tail, d.head)}).Connected)
    (hroom : totalSelected (initialVertexRestrict hD θ) + 1 ≤
      ((F.induced hD (Fin.succOrderEmb (k + 1))).goodEdges
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))).card) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      SelectedConnected (initialVertexRestrict hD η) ∧
      (fullSelection η).filter (fun q => q.tail = 0) =
        ((fullSelection θ).filter (fun q => q.tail = 0)).erase e := by
  let ι := Fin.succOrderEmb (k + 1)
  let E := inducedDiagram hD ι
  let F' := F.induced hD ι
  have hE := inducedDiagram_forward hD ι
  have hα := F.anchor_inducedRestrict_of_closed hD ι (F.initialVertex_step_closed hD) θ hθ
  have hlower : k + 1 ≤ totalSelected (initialVertexRestrict hD θ) + 1 := by
    have hG : (edgeSetGraph (fullSelection (initialVertexRestrict hD θ))).Connected :=
      ⟨(edgeSetGraph_fullSelection_preconnected_iff _).mpr hc⟩
    have hcard := hG.card_vert_le_card_edgeSet_add_one
    rw [edgeSetGraph_card hE, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    exact hcard
  obtain ⟨α, ha, hca, hcount, hd⟩ := F'.exists_connected_anchor_card_avoiding hE
    d hdG hdF hrem (totalSelected (initialVertexRestrict hD θ)) hlower hroom
  have hp := hunique (initialVertexRestrict hD θ) α
    (F'.commonCover_of_anchor hE hα) (F'.commonCover_of_anchor hE ha) hc hca hcount.symm
  let ζ := initialVertexExtend hD θ α
  have hθζ : Relation.ReflTransGen (Flip D) θ ζ := initialVertex_lift_reachable hD θ α hp
  have hζ : F.Anchor hD ζ := F.initialVertex_anchor_extend hD θ hθ α ha
  have hrestrict : initialVertexRestrict hD ζ = α := initialVertexRestrict_extend hD θ α
  have heζ : e ∈ fullSelection ζ := by
    rw [mem_fullSelection_iff_selected]
    change D.edgeData.selected (initialVertexExtend hD θ α).val e.tail e.head
    rw [het, initialVertexExtend_selected_zero_iff]
    simpa only [het] using (mem_fullSelection_iff_selected θ e).mp he
  have hdζ : inducedEdge hD ι d ∉ fullSelection ζ := by
    intro h
    have hsel := (inducedRestrict_mem_fullSelection_iff hD ι ζ d).mpr h
    change d ∈ fullSelection (initialVertexRestrict hD ζ) at hsel
    rw [hrestrict] at hsel
    exact hd hsel
  obtain ⟨η, hζη, hη, hfull⟩ := F.exists_forwardCopyExchange hD ζ hζ e
    (inducedEdge hD ι d) hlink hegood heζ hdζ
  refine ⟨η, hθζ.trans hζη, hη, ?_, ?_⟩
  · apply initialVertex_connected_of_exchange hD ζ η e het d hfull
    simpa only [hrestrict] using hca
  · rw [initialVertex_row_of_exchange hD ζ η e d hfull]
    change ((fullSelection (initialVertexExtend hD θ α)).filter
      (fun q => q.tail = 0)).erase e = _
    rw [initialVertexExtend_row]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

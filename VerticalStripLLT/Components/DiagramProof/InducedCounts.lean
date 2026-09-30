import VerticalStripLLT.Components.DiagramProof.InducedDecorations
import VerticalStripLLT.Components.DiagramProof.InducedRestriction

/-! Selected-edge counts under restriction to an induced diagram. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

theorem inducedRestrict_image_fullSelection (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (θ : Orientation D) :
    (fullSelection
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ)).image
        (inducedEdgeEmbedding hD ι) =
      (fullSelection θ).filter
        (fun e : Edge D.area => ∃ u v, ι u = e.tail ∧ ι v = e.head) := by
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply (mem_fullSelection_iff_selected θ _).mpr
      change D.edgeData.selected θ.val (inducedEdge hD ι f).tail (inducedEdge hD ι f).head
      rw [inducedEdge_tail, inducedEdge_head]
      exact (inducedRestrict_selected (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ f.tail f.head).mp
        ((mem_fullSelection_iff_selected _ f).mp hf)
    · exact ⟨f.tail, f.head, (inducedEdge_tail hD ι f).symm,
        (inducedEdge_head hD ι f).symm⟩
  · rintro he
    obtain ⟨hefull, u, v, hu, hv⟩ := Finset.mem_filter.mp he
    obtain ⟨f, hft, hfh⟩ :=
      (inducedDiagram_naturalEdge_iff hD ι u v).mpr
        ⟨e, hu.symm, hv.symm⟩
    have hef : inducedEdge hD ι f = e := by
      apply D.endpointEmbedding.injective
      apply Prod.ext
      · exact (inducedEdge_tail hD ι f).trans
          ((congrArg ι hft).trans hu)
      · exact (inducedEdge_head hD ι f).trans
          ((congrArg ι hfh).trans hv)
    refine Finset.mem_image.mpr ⟨f, ?_, hef⟩
    apply (mem_fullSelection_iff_selected _ f).mpr
    rw [inducedRestrict_selected (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ]
    simpa only [hft, hfh, hu, hv] using
      (mem_fullSelection_iff_selected θ e).mp hefull

theorem inducedRestrict_totalSelected_eq_filter (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (θ : Orientation D) :
    totalSelected
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ) =
      ((fullSelection θ).filter
        (fun e : Edge D.area => ∃ u v, ι u = e.tail ∧ ι v = e.head)).card := by
  calc
    totalSelected
        (inducedRestrict (inducedDiagram_forward hD ι) ι
          (inducedDiagram_naturalEdge_iff hD ι)
          (inducedDiagram_strictEndpoint_iff hD ι) θ) =
        ((fullSelection
          (inducedRestrict (inducedDiagram_forward hD ι) ι
            (inducedDiagram_naturalEdge_iff hD ι)
            (inducedDiagram_strictEndpoint_iff hD ι) θ)).image
          (inducedEdgeEmbedding hD ι)).card := by
      symm
      exact Finset.card_image_of_injective _ (inducedEdgeEmbedding hD ι).injective
    _ = ((fullSelection θ).filter
        (fun e : Edge D.area => ∃ u v, ι u = e.tail ∧ ι v = e.head)).card := by
      rw [inducedRestrict_image_fullSelection]

theorem totalSelected_eq_inducedRestrict_add_outside (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (θ : Orientation D) :
    totalSelected θ =
      totalSelected
          (inducedRestrict (inducedDiagram_forward hD ι) ι
            (inducedDiagram_naturalEdge_iff hD ι)
            (inducedDiagram_strictEndpoint_iff hD ι) θ) +
        ((fullSelection θ).filter
          (fun e : Edge D.area =>
            ¬ ∃ u v, ι u = e.tail ∧ ι v = e.head)).card := by
  rw [inducedRestrict_totalSelected_eq_filter]
  simpa only [totalSelected] using
    (Finset.card_filter_add_card_filter_not
      (fun e : Edge D.area => ∃ u v, ι u = e.tail ∧ ι v = e.head)
      (s := fullSelection θ)).symm

end

end VerticalStripLLT.Circular.DiagramProof

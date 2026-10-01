import VerticalStripLLT.Components.DiagramProof.Restriction.InducedCorners

/-! Inherited strict corners on an induced natural diagram. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

variable (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)

/-- The induced diagram inherits exactly the strict edges whose ambient lifts are strict. -/
def inducedDiagram : Diagram (k + 1) where
  area := (inducedUndecorated hD ι).area
  strict := Finset.univ.filter (fun e => inducedEdge hD ι e ∈ D.strict)
  strict_corner := by
    intro e he
    apply isCorner_of_inducedEdge_isCorner hD ι e
    exact D.strict_corner _ (Finset.mem_filter.mp he).2

@[simp]
theorem mem_inducedDiagram_strict (e : Edge (inducedDiagram hD ι).area) :
    e ∈ (inducedDiagram hD ι).strict ↔ inducedEdge hD ι e ∈ D.strict := by
  change e ∈ Finset.univ.filter (fun f : Edge (inducedUndecorated hD ι).area =>
    inducedEdge hD ι f ∈ D.strict) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

/-- The edge map of the induced diagram into the ambient diagram. -/
def inducedEdgeEmbedding :
    Edge (inducedDiagram hD ι).area ↪ Edge D.area :=
  ⟨inducedEdge hD ι, inducedEdge_injective hD ι⟩

/-- Induced diagrams are forward. -/
theorem inducedDiagram_forward : Forward (inducedDiagram hD ι) := by
  intro e
  exact inducedUndecorated_forward hD ι e

theorem inducedDiagram_naturalEdge_iff (u v : Fin (k + 1)) :
    (∃ e : Edge (inducedDiagram hD ι).area,
      e.tail = u ∧ e.head = v) ↔
      ∃ f : Edge D.area, f.tail = ι u ∧ f.head = ι v := by
  exact inducedUndecorated_naturalEdge_iff hD ι u v

theorem inducedDiagram_strictEndpoint_iff (u v : Fin (k + 1)) :
    (∃ e ∈ (inducedDiagram hD ι).strict,
      e.tail = u ∧ e.head = v) ↔
      ∃ f ∈ D.strict, f.tail = ι u ∧ f.head = ι v := by
  constructor
  · rintro ⟨e, he, rfl, rfl⟩
    exact ⟨inducedEdge hD ι e, (mem_inducedDiagram_strict hD ι e).mp he,
      inducedEdge_tail hD ι e, inducedEdge_head hD ι e⟩
  · rintro ⟨f, hf, ht, hh⟩
    obtain ⟨e, hte, hhe⟩ :=
      (inducedUndecorated_naturalEdge_iff hD ι u v).mpr ⟨f, ht, hh⟩
    have hef : inducedEdge hD ι e = f := by
      apply D.endpointEmbedding.injective
      apply Prod.ext
      · exact (inducedEdge_tail hD ι e).trans
          ((congrArg ι hte).trans ht.symm)
      · exact (inducedEdge_head hD ι e).trans
          ((congrArg ι hhe).trans hh.symm)
    refine ⟨e, (mem_inducedDiagram_strict hD ι e).mpr ?_, hte, hhe⟩
    simpa only [hef] using hf

theorem inducedDiagram_map_strict :
    (inducedDiagram hD ι).strict.map (inducedEdgeEmbedding hD ι) =
      D.strict.filter (fun f => ∃ u v, ι u = f.tail ∧ ι v = f.head) := by
  ext f
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨(mem_inducedDiagram_strict hD ι e).mp he,
      e.tail, e.head, (inducedEdge_tail hD ι e).symm,
      (inducedEdge_head hD ι e).symm⟩
  · rintro ⟨hf, u, v, hu, hv⟩
    obtain ⟨e, hte, hhe⟩ :=
      (inducedUndecorated_naturalEdge_iff hD ι u v).mpr ⟨f, hu.symm, hv.symm⟩
    have hef : inducedEdge hD ι e = f := by
      apply D.endpointEmbedding.injective
      apply Prod.ext
      · exact (inducedEdge_tail hD ι e).trans
          ((congrArg ι hte).trans hu)
      · exact (inducedEdge_head hD ι e).trans
          ((congrArg ι hhe).trans hv)
    exact ⟨e, (mem_inducedDiagram_strict hD ι e).mpr (by simpa only [hef] using hf), hef⟩

end

end VerticalStripLLT.Circular.DiagramProof

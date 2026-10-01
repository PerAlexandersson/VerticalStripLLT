import VerticalStripLLT.Components.DiagramProof.InitialVertexCounts

/-! Extending a core orientation while preserving the initial row. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

/-- Replace the selected relation on the vertices after zero by a core orientation. -/
def initialVertexExtend (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) : Orientation D :=
  inducedExtend hD (Fin.succOrderEmb (k + 1))
    (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
    (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ α

theorem initialVertexExtend_inside (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))))
    (u v : Fin (k + 1)) :
    D.edgeData.selected (initialVertexExtend hD θ α).val u.succ v.succ ↔
      (inducedDiagram hD (Fin.succOrderEmb (k + 1))).edgeData.selected α.val u v := by
  exact inducedExtend_inside hD (Fin.succOrderEmb (k + 1))
    (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
    (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ α u v

theorem initialVertexExtend_selected_zero_iff (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) (v : Fin (k + 2)) :
    D.edgeData.selected (initialVertexExtend hD θ α).val 0 v ↔
      D.edgeData.selected θ.val 0 v := by
  apply inducedExtend_outside hD (Fin.succOrderEmb (k + 1))
    (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
    (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ α 0 v
  rintro ⟨a, _, ha, _⟩
  exact Fin.succ_ne_zero a ha

theorem initialVertexRestrict_extend (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) :
    initialVertexRestrict hD (initialVertexExtend hD θ α) = α := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    initialVertexRestrict_selected]
  exact initialVertexExtend_inside hD θ α e.tail e.head

theorem initialVertexExtend_row (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) :
    (fullSelection (initialVertexExtend hD θ α)).filter (fun e => e.tail = 0) =
      (fullSelection θ).filter (fun e => e.tail = 0) := by
  ext e
  simp only [Finset.mem_filter]
  by_cases ht : e.tail = 0
  · simp only [ht, and_true, mem_fullSelection_iff_selected,
      initialVertexExtend_selected_zero_iff]
  · simp only [ht, and_false]

theorem initialVertexExtend_totalSelected (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) :
    totalSelected (initialVertexExtend hD θ α) =
      totalSelected α + ((fullSelection θ).filter (fun e => e.tail = 0)).card := by
  rw [initialVertex_totalSelected, initialVertexRestrict_extend, initialVertexExtend_row]

namespace CornerFamily

/-- A closed corner family remains an anchor after replacing its positive-vertex core. -/
theorem initialVertex_anchor_extend (F : CornerFamily D) (hD : Forward D)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))))
    (hα : (F.induced hD (Fin.succOrderEmb (k + 1))).Anchor
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) α) :
    F.Anchor hD (initialVertexExtend hD θ α) := by
  apply F.anchor_of_induced_replacement_of_closed hD (Fin.succOrderEmb (k + 1))
    (F.initialVertex_step_closed hD) θ (initialVertexExtend hD θ α) hθ α hα
  · intro u v
    simpa only [Fin.coe_succOrderEmb] using initialVertexExtend_inside hD θ α u v
  · intro u v hout
    exact inducedExtend_outside hD (Fin.succOrderEmb (k + 1))
      (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
      (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ α u v hout

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof

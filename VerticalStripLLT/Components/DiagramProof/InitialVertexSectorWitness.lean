import VerticalStripLLT.Components.DiagramProof.InitialVertexExtras
import VerticalStripLLT.Components.DiagramProof.InitialVertexExtension

/-! Anchors with a prescribed sector of selected initial-row extras. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

namespace CornerFamily

variable {k : ℕ} {D : Diagram (k + 2)}

/-- Any prescribed subset of the initial-row extras extends an actual core anchor. -/
theorem exists_initialVertex_sector_witness (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (S : Finset (Edge D.area)) (hS : S ⊆ F.initialVertexExtras hD f)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))))
    (hα : (F.induced hD (Fin.succOrderEmb (k + 1))).Anchor
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) α) :
    ∃ θ : Orientation D, F.Anchor hD θ ∧ initialVertexRestrict hD θ = α ∧
      (fullSelection θ).filter (fun e => e.tail = 0) = insert f S := by
  let β := ofFullSelection hD (F.edges ∪ S)
    (F.contains_strict.trans Finset.subset_union_left)
  have hgood : F.edges ∪ S ⊆ F.goodEdges hD := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (F.mem_goodEdges hD e).mpr (Or.inl he)
    · exact (Finset.mem_filter.mp (hS he)).1
  have hβ : F.Anchor hD β :=
    F.anchor_ofFullSelection hD (F.edges ∪ S) Finset.subset_union_left hgood
  have hβrow : (fullSelection β).filter (fun e => e.tail = 0) = insert f S := by
    rw [fullSelection_ofFullSelection]
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨he, ht⟩
      rcases Finset.mem_union.mp he with he | he
      · have heq : e = f := by
          have hh := F.step_rightUnique
            ((F.step_iff _ _).mpr ⟨e, he, rfl, rfl⟩)
            ((F.step_iff _ _).mpr ⟨f, hf, hft.trans ht.symm, rfl⟩)
          exact D.endpointEmbedding.injective (Prod.ext (ht.trans hft.symm) hh)
        simpa only [heq] using Finset.mem_insert_self f S
      · exact Finset.mem_insert_of_mem he
    · intro he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf, hft⟩
      · have heS := Finset.mem_filter.mp (hS he)
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ he, heS.2.1⟩
  let θ := initialVertexExtend hD β α
  refine ⟨θ, F.initialVertex_anchor_extend hD β hβ α hα, ?_, ?_⟩
  · exact initialVertexRestrict_extend hD β α
  · rw [show θ = initialVertexExtend hD β α from rfl, initialVertexExtend_row, hβrow]

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof

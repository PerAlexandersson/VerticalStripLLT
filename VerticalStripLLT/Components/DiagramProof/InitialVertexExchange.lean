import VerticalStripLLT.Components.DiagramProof.InitialVertexCounts
import VerticalStripLLT.Components.DiagramProof.WeakBlocks

/-! The exact initial row and core after sliding an initial edge into the core. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {k : ℕ} {D : Diagram (k + 2)}

theorem initialVertex_selected_row_iff (θ η : Orientation D)
    (hrow : (fullSelection θ).filter (fun e => e.tail = 0) =
      (fullSelection η).filter (fun e => e.tail = 0)) (v : Fin (k + 2)) :
    D.edgeData.selected θ.val 0 v ↔ D.edgeData.selected η.val 0 v := by
  constructor
  · rintro ⟨e, he, ht, hh⟩
    have hm : e ∈ (fullSelection θ).filter (fun q => q.tail = 0) :=
      Finset.mem_filter.mpr ⟨he, ht⟩
    rw [hrow] at hm
    exact ⟨e, (Finset.mem_filter.mp hm).1, ht, hh⟩
  · rintro ⟨e, he, ht, hh⟩
    have hm : e ∈ (fullSelection η).filter (fun q => q.tail = 0) :=
      Finset.mem_filter.mpr ⟨he, ht⟩
    rw [← hrow] at hm
    exact ⟨e, (Finset.mem_filter.mp hm).1, ht, hh⟩

/-- The crossing slide deletes its initial edge and leaves every other initial edge fixed. -/
theorem initialVertex_row_of_exchange (hD : Forward D) (θ η : Orientation D)
    (e : Edge D.area) (d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area)
    (hfull : fullSelection η =
      insert (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) ((fullSelection θ).erase e)) :
    (fullSelection η).filter (fun q => q.tail = 0) =
      ((fullSelection θ).filter (fun q => q.tail = 0)).erase e := by
  have hd : (inducedEdge hD (Fin.succOrderEmb (k + 1)) d).tail ≠ 0 := by
    rw [inducedEdge_tail]
    exact Fin.succ_ne_zero d.tail
  ext q
  simp only [hfull, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  grind

/-- Its core gains exactly the matching edge; no core edge is removed. -/
theorem initialVertex_restrict_of_exchange (hD : Forward D) (θ η : Orientation D)
    (e : Edge D.area) (het : e.tail = 0)
    (d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area)
    (hfull : fullSelection η =
      insert (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) ((fullSelection θ).erase e)) :
    fullSelection (initialVertexRestrict hD η) =
      insert d (fullSelection (initialVertexRestrict hD θ)) := by
  let ι := Fin.succOrderEmb (k + 1)
  ext q
  have hqe : inducedEdge hD ι q ≠ e := by
    intro heq
    have ht := (congrArg Edge.tail heq).trans het
    rw [inducedEdge_tail] at ht
    exact Fin.succ_ne_zero q.tail ht
  change q ∈ fullSelection (initialVertexRestrict hD η) ↔
    q ∈ insert d (fullSelection (initialVertexRestrict hD θ))
  rw [show q ∈ fullSelection (initialVertexRestrict hD η) ↔
      inducedEdge hD ι q ∈ fullSelection η from
    inducedRestrict_mem_fullSelection_iff hD ι η q]
  rw [hfull, Finset.mem_insert, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl (inducedEdge_injective hD ι h)
    · exact Or.inr ((inducedRestrict_mem_fullSelection_iff hD ι θ q).mpr h)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨hqe, (inducedRestrict_mem_fullSelection_iff hD ι θ q).mp h⟩

/-- Once the core is connected, the same crossing slide keeps it connected. -/
theorem initialVertex_connected_of_exchange (hD : Forward D) (θ η : Orientation D)
    (e : Edge D.area) (het : e.tail = 0)
    (d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area)
    (hfull : fullSelection η =
      insert (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) ((fullSelection θ).erase e))
    (hc : SelectedConnected (initialVertexRestrict hD θ)) :
    SelectedConnected (initialVertexRestrict hD η) := by
  intro u v
  apply Relation.EqvGen.mono ?_ u v (hc u v)
  rintro x y ⟨q, hq, hqt, hqh⟩
  refine ⟨q, ?_, hqt, hqh⟩
  change q ∈ fullSelection (initialVertexRestrict hD η)
  rw [initialVertex_restrict_of_exchange hD θ η e het d hfull]
  exact Finset.mem_insert_of_mem hq

end VerticalStripLLT.Circular.DiagramProof

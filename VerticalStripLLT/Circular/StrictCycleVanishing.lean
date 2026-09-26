import VerticalStripLLT.Circular.HRV
import VerticalStripLLT.Circular.StrictCycle
import VerticalStripLLT.ShiftEvaluation

/-! Vanishing from a strict directed cycle, for arbitrary circular diagrams. -/

namespace VerticalStripLLT.Circular

variable {n : ℕ}

private theorem selected_cycle_of_strict_cycle (D : Diagram n)
    {A : Finset (Edge D.area)}
    {u v : Fin n}
    (hcycle : Relation.TransGen (D.edgeData.selected ∅) u v) :
    Relation.TransGen (D.edgeData.selected A) u v := by
  induction hcycle with
  | single hstep =>
    rcases hstep with ⟨e, he, hu, hv⟩
    have he' : e ∈ D.edgeData.strict := by simpa using he
    exact Relation.TransGen.single ⟨e, Finset.mem_union_left _ he', hu, hv⟩
  | tail _ hstep ih =>
    exact Relation.TransGen.tail ih (by
      rcases hstep with ⟨e, he, hu, hv⟩
      have he' : e ∈ D.edgeData.strict := by simpa using he
      exact ⟨e, Finset.mem_union_left _ he', hu, hv⟩)

theorem coloringLLT_eq_zero_of_not_admissible_empty (D : Diagram n)
    (h : ¬ D.edgeData.Admissible ∅) (m : ℕ) : D.edgeData.coloringLLT m = 0 := by
  classical
  unfold EdgeData.coloringLLT
  apply Finset.sum_eq_zero
  intro c _
  have hc : ¬ D.edgeData.admissibleColoring c := by
    simpa [EdgeData.admissibleColoring] using
      D.edgeData.not_selected_coloring_of_not_admissible ∅ h c
  simp [EdgeData.coloringWeight, hc]

theorem shiftedOrientationExpansion_eq_zero_of_not_admissible_empty (D : Diagram n)
    (h : ¬ D.edgeData.Admissible ∅) : shiftedOrientationExpansion D = 0 := by
  classical
  let : IsEmpty (Orientation D) := ⟨fun θ => by
    apply h
    intro v hcycle
    exact θ.property.2 v (selected_cycle_of_strict_cycle D hcycle)⟩
  simp [shiftedOrientationExpansion]

theorem coloringLLT_shifted_eq_expansion_of_not_admissible_empty (D : Diagram n)
    (h : ¬ D.edgeData.Admissible ∅) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  rw [Diagram.coloringLLT,
    coloringLLT_eq_zero_of_not_admissible_empty D h m,
    shiftedOrientationExpansion_eq_zero_of_not_admissible_empty D h, map_zero,
    map_zero]

end VerticalStripLLT.Circular

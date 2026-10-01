import VerticalStripLLT.Components.DiagramProof.Complete.Diagram
import VerticalStripLLT.Components.DiagramProof.Foundation.SelectedRelation
import VerticalStripLLT.Components.DiagramProof.Restriction.CoreExtension

/-! Complete subdiagrams with their actual selected states and fixed exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} (ι : Fin (k + 1) ↪o Fin (n + 1))

/-- Restrict an actual complete-diagram state along an increasing vertex embedding. -/
def completeRestrictAlong (θ : Orientation (completeDiagram n)) :
    Orientation (completeDiagram k) :=
  ofSelectedRelation (complete_forward k)
    (fun u v => (completeDiagram n).edgeData.selected θ.val (ι u) (ι v))
    (by
      intro u v h
      exact (complete_naturalEdge_iff k u v).mpr
        (ι.lt_iff_lt.mp (θ.selected_lt_of_forward (complete_forward n) h)))
    (by simp)

@[simp]
theorem completeRestrictAlong_selected (θ : Orientation (completeDiagram n))
    (u v : Fin (k + 1)) :
    (completeDiagram k).edgeData.selected (completeRestrictAlong ι θ).val u v ↔
      (completeDiagram n).edgeData.selected θ.val (ι u) (ι v) :=
  selected_ofSelectedRelation ..

/-- Replace only the selected edges with both endpoints in the smaller diagram. -/
def completeExtendAlong (θ : Orientation (completeDiagram n))
    (α : Orientation (completeDiagram k)) : Orientation (completeDiagram n) :=
  ofSelectedRelation (complete_forward n)
    (fun u v =>
      (∃ a b, ι a = u ∧ ι b = v ∧ (completeDiagram k).edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ (completeDiagram n).edgeData.selected θ.val u v))
    (by
      intro u v h
      apply (complete_naturalEdge_iff n u v).mpr
      rcases h with ⟨a, b, rfl, rfl, hab⟩ | ⟨_, huv⟩
      · exact ι.strictMono (α.selected_lt_of_forward (complete_forward k) hab)
      · exact θ.selected_lt_of_forward (complete_forward n) huv)
    (by simp)

@[simp]
theorem completeExtendAlong_selected (θ : Orientation (completeDiagram n))
    (α : Orientation (completeDiagram k)) (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (completeExtendAlong ι θ α).val u v ↔
      (∃ a b, ι a = u ∧ ι b = v ∧ (completeDiagram k).edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ (completeDiagram n).edgeData.selected θ.val u v) :=
  selected_ofSelectedRelation ..

@[simp]
theorem completeExtendAlong_inside (θ : Orientation (completeDiagram n))
    (α : Orientation (completeDiagram k)) (u v : Fin (k + 1)) :
    (completeDiagram n).edgeData.selected (completeExtendAlong ι θ α).val (ι u) (ι v) ↔
      (completeDiagram k).edgeData.selected α.val u v := by
  rw [completeExtendAlong_selected]
  simp [ι.injective.eq_iff]

theorem completeExtendAlong_outside (θ : Orientation (completeDiagram n))
    (α : Orientation (completeDiagram k)) (u v : Fin (n + 1))
    (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
    (completeDiagram n).edgeData.selected (completeExtendAlong ι θ α).val u v ↔
      (completeDiagram n).edgeData.selected θ.val u v := by
  rw [completeExtendAlong_selected]
  have hno : ¬ ∃ a b, ι a = u ∧ ι b = v ∧
      (completeDiagram k).edgeData.selected α.val a b := by
    rintro ⟨a, b, ha, hb, _⟩
    exact hout ⟨a, b, ha, hb⟩
  simp only [hno, hout, not_false_eq_true, true_and, false_or]

@[simp]
theorem completeExtendAlong_restrict (θ : Orientation (completeDiagram n)) :
    completeExtendAlong ι θ (completeRestrictAlong ι θ) = θ := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    completeExtendAlong_selected]
  constructor
  · rintro (⟨a, b, ha, hb, hab⟩ | ⟨_, h⟩)
    · rw [completeRestrictAlong_selected] at hab
      simpa only [ha, hb] using hab
    · exact h
  · intro he
    by_cases h : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨a, b, ha, hb⟩ := h
      exact Or.inl ⟨a, b, ha, hb, (completeRestrictAlong_selected ι θ a b).mpr
        (by simpa only [ha, hb] using he)⟩
    · exact Or.inr ⟨h, he⟩

/-- Replacing the core of one state by another reconstructs that state when exteriors agree. -/
theorem completeExtendAlong_eq_of_outside (θ η : Orientation (completeDiagram n))
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v)) :
    completeExtendAlong ι θ (completeRestrictAlong ι η) = η := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
  by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
  · obtain ⟨a, b, ha, hb⟩ := hcore
    rw [← ha, ← hb, completeExtendAlong_inside, completeRestrictAlong_selected]
  · exact (completeExtendAlong_outside ι θ _ _ _ hcore).trans (houtside _ _ hcore)

/-- A path in the smaller diagram lifts once all ambient cover tests restrict exactly. -/
theorem complete_liftAlong_reachable (θ : Orientation (completeDiagram n))
    (hcovers : ∀ α u v,
      Cover (completeExtendAlong ι θ α) (ι u) (ι v) ↔ Cover α u v)
    {α : Orientation (completeDiagram k)}
    (h : Relation.ReflTransGen (Flip (completeDiagram k)) (completeRestrictAlong ι θ) α) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ (completeExtendAlong ι θ α) := by
  have hp := CoreExtension.lift_reachable_of_cover_iff (complete_forward n) (complete_forward k)
    ι (completeExtendAlong ι θ) (completeExtendAlong_inside ι θ)
    (fun α β u v hout => (completeExtendAlong_outside ι θ α u v hout).trans
      (completeExtendAlong_outside ι θ β u v hout).symm) hcovers h
  simpa only [completeExtendAlong_restrict] using hp

end

end VerticalStripLLT.Circular.DiagramProof

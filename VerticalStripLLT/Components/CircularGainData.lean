import VerticalStripLLT.Components.GainContraction
import VerticalStripLLT.Circular.HRVPotential

/-! The gain graph underlying a circular diagram. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

variable {n : ℕ}

/-- The natural gain attached to a circular diagram edge is its length. -/
abbrev naturalGain (D : Diagram n) : Components.GainData (Fin n) (Edge D.area) where
  tail := Edge.tail
  head := Edge.head
  gain := fun e => (e.length.val : ℤ)

/-- The gain-selected relation is the circular selected-edge relation. -/
theorem selectedRelation_naturalGain_iff (D : Diagram n)
    (A : Finset (Edge D.area)) (u v : Fin n) :
    (naturalGain D).selectedRelation (D.strict ∪ A) u v ↔
      D.edgeData.selected A u v := by
  rfl

end Diagram

namespace Orientation

variable {n : ℕ} {D : Diagram n}

/-- Restrict an orientation to an arbitrary edge set. -/
noncomputable def subselection (θ : Orientation D) (X : Finset (Edge D.area)) : Orientation D :=
  ⟨θ.val ∩ X, Finset.inter_subset_left.trans θ.property.1,
    D.admissible_mono Finset.inter_subset_left θ.property.2⟩

@[simp]
theorem val_subselection (θ : Orientation D) (X : Finset (Edge D.area)) :
    (subselection θ X).val = θ.val ∩ X := rfl

theorem val_subselection_eq (θ : Orientation D) (X : Finset (Edge D.area))
    (hX : X ⊆ θ.val) :
    (subselection θ X).val = X := by
  rw [val_subselection]
  exact Finset.inter_eq_right.mpr hX

/-- The natural gain graph selected by an orientation is acyclic. -/
theorem naturalGain_selected_acyclic (θ : Orientation D) :
    ∀ v, ¬Relation.TransGen
      ((Diagram.naturalGain D).selectedRelation (D.strict ∪ θ.val)) v v := by
  intro v hv
  apply θ.property.2 v
  refine Relation.TransGen.mono ?_ _ _ hv
  intro u w h
  exact (Diagram.selectedRelation_naturalGain_iff D θ.val u w).mp h

/-- Every restricted orientation also gives an acyclic natural gain graph. -/
theorem naturalGain_subselection_acyclic (θ : Orientation D)
    (X : Finset (Edge D.area)) :
    ∀ v, ¬Relation.TransGen
      ((Diagram.naturalGain D).selectedRelation
        (D.strict ∪ (subselection θ X).val)) v v := by
  intro v hv
  apply (subselection θ X).property.2 v
  refine Relation.TransGen.mono ?_ _ _ hv
  intro u w h
  exact (Diagram.selectedRelation_naturalGain_iff D (subselection θ X).val u w).mp h

end Orientation

end VerticalStripLLT.Circular

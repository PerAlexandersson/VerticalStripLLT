import VerticalStripLLT.Components.DiagramProof.CompleteDiagram
import VerticalStripLLT.Components.DiagramProof.SelectedRelation
import VerticalStripLLT.Components.DiagramProof.CoreExtension
import VerticalStripLLT.Components.DiagramProof.CornerTransport

/-! Actual complete cores of ordinary diagrams, with the exterior selection retained. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Restrict the selected relation to an increasing list of vertices in a complete core. -/
def cliqueRestrict (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (θ : Orientation D) :
    Orientation (completeDiagram k) :=
  ofSelectedRelation (complete_forward k)
    (fun u v => D.edgeData.selected θ.val (ι u) (ι v))
    (by
      intro u v h
      exact (complete_naturalEdge_iff k u v).mpr
        (ι.lt_iff_lt.mp (θ.selected_lt_of_forward hD h)))
    (by simp)

@[simp]
theorem cliqueRestrict_selected (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (θ : Orientation D) (u v : Fin (k + 1)) :
    (completeDiagram k).edgeData.selected (cliqueRestrict hD ι θ).val u v ↔
      D.edgeData.selected θ.val (ι u) (ι v) := selected_ofSelectedRelation ..

/-- Replace the selected core and retain every exterior edge. Strict decorations are restored
after lifting the path by the proved whole-component marking equivalence. -/
def cliqueExtend (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) (α : Orientation (completeDiagram k)) : Orientation D.undecorated :=
  ofSelectedRelation hD
    (fun u v =>
      (∃ a b, ι a = u ∧ ι b = v ∧ (completeDiagram k).edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ D.edgeData.selected θ.val u v))
    (by
      intro u v h
      rcases h with ⟨a, b, rfl, rfl, hab⟩ | ⟨_, e, _, ht, hh⟩
      · exact hnatural a b (α.selected_lt_of_forward (complete_forward k) hab)
      · exact ⟨e, ht, hh⟩)
    (by intro e he; exact (Finset.notMem_empty e he).elim)

@[simp]
theorem cliqueExtend_selected (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) (α : Orientation (completeDiagram k)) (u v : Fin n) :
    D.undecorated.edgeData.selected (cliqueExtend hD ι hnatural θ α).val u v ↔
      (∃ a b, ι a = u ∧ ι b = v ∧ (completeDiagram k).edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ D.edgeData.selected θ.val u v) :=
  selected_ofSelectedRelation ..

@[simp]
theorem cliqueExtend_inside (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) (α : Orientation (completeDiagram k)) (u v : Fin (k + 1)) :
    D.undecorated.edgeData.selected (cliqueExtend hD ι hnatural θ α).val (ι u) (ι v) ↔
      (completeDiagram k).edgeData.selected α.val u v := by
  rw [cliqueExtend_selected]
  simp [ι.injective.eq_iff]

theorem cliqueExtend_outside (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) (α : Orientation (completeDiagram k)) (u v : Fin n)
    (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
    D.undecorated.edgeData.selected (cliqueExtend hD ι hnatural θ α).val u v ↔
      D.edgeData.selected θ.val u v := by
  rw [cliqueExtend_selected]
  have hno : ¬ ∃ a b, ι a = u ∧ ι b = v ∧
      (completeDiagram k).edgeData.selected α.val a b := by
    rintro ⟨a, b, ha, hb, _⟩
    exact hout ⟨a, b, ha, hb⟩
  simp only [hno, hout, not_false_eq_true, true_and, false_or]

@[simp]
theorem cliqueExtend_restrict (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) :
    cliqueExtend hD ι hnatural θ (cliqueRestrict hD ι θ) = θ.toUndecorated := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    θ.toUndecorated_selected, cliqueExtend_selected]
  constructor
  · rintro (⟨a, b, ha, hb, hab⟩ | ⟨_, h⟩)
    · rw [cliqueRestrict_selected] at hab
      simpa only [ha, hb] using hab
    · exact h
  · intro he
    by_cases h : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨a, b, ha, hb⟩ := h
      exact Or.inl ⟨a, b, ha, hb, (cliqueRestrict_selected hD ι θ a b).mpr
        (by simpa only [ha, hb] using he)⟩
    · exact Or.inr ⟨h, he⟩

/-- Equal exterior selections identify the extension with the intended actual target. -/
theorem cliqueExtend_eq_of_outside (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ η : Orientation D)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v)) :
    cliqueExtend hD ι hnatural θ (cliqueRestrict hD ι η) = η.toUndecorated := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    η.toUndecorated_selected]
  by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
  · obtain ⟨a, b, ha, hb⟩ := hcore
    rw [← ha, ← hb, cliqueExtend_inside, cliqueRestrict_selected]
  · exact (cliqueExtend_outside hD ι hnatural θ _ _ _ hcore).trans (houtside _ _ hcore)

/-- A core path produces an actual ambient endpoint with that core and the original exterior. -/
theorem clique_lift_core_reachable (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D)
    (hcovers : ∀ α u v,
      Cover (cliqueExtend hD ι hnatural θ α) (ι u) (ι v) ↔ Cover α u v)
    (α : Orientation (completeDiagram k))
    (hp : Relation.ReflTransGen (Flip (completeDiagram k)) (cliqueRestrict hD ι θ) α) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ u v, D.edgeData.selected η.val (ι u) (ι v) ↔
        (completeDiagram k).edgeData.selected α.val u v) ∧
      (∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
        (D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v)) := by
  have h := CoreExtension.lift_reachable_of_cover_iff (D := D.undecorated) hD (complete_forward k)
    ι (cliqueExtend hD ι hnatural θ) (cliqueExtend_inside hD ι hnatural θ)
    (fun α β u v hout => (cliqueExtend_outside hD ι hnatural θ α u v hout).trans
      (cliqueExtend_outside hD ι hnatural θ β u v hout).symm) hcovers hp
  rw [cliqueExtend_restrict] at h
  obtain ⟨η, hθη, hη⟩ := exists_original_of_undecorated_reachable h
  have hselected : D.edgeData.selected η.val =
      D.undecorated.edgeData.selected (cliqueExtend hD ι hnatural θ α).val := by
    rw [← hη, η.toUndecorated_selected]
  refine ⟨η, hθη, ?_, ?_⟩
  · intro u v
    rw [hselected]
    exact cliqueExtend_inside hD ι hnatural θ α u v
  · intro u v hout
    rw [hselected]
    exact cliqueExtend_outside hD ι hnatural θ α u v hout

/-- Exact cover restriction lifts an actual complete-core path, with every strict decoration
restored in the original ambient diagram. -/
theorem clique_lift_reachable (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ η : Orientation D)
    (hcovers : ∀ α u v,
      Cover (cliqueExtend hD ι hnatural θ α) (ι u) (ι v) ↔ Cover α u v)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v))
    (hp : Relation.ReflTransGen (Flip (completeDiagram k))
      (cliqueRestrict hD ι θ) (cliqueRestrict hD ι η)) :
    Relation.ReflTransGen (Flip D) θ η := by
  apply reachable_toUndecorated_iff.mp
  have h := CoreExtension.lift_reachable_of_cover_iff (D := D.undecorated) hD (complete_forward k)
    ι (cliqueExtend hD ι hnatural θ) (cliqueExtend_inside hD ι hnatural θ)
    (fun α β u v hout => (cliqueExtend_outside hD ι hnatural θ α u v hout).trans
      (cliqueExtend_outside hD ι hnatural θ β u v hout).symm) hcovers hp
  simpa only [cliqueExtend_restrict,
    cliqueExtend_eq_of_outside hD ι hnatural θ η houtside] using h

end

end VerticalStripLLT.Circular.DiagramProof

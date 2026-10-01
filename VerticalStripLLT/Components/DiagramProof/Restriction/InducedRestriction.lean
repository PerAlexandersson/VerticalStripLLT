import VerticalStripLLT.Components.DiagramProof.Foundation.SelectedRelation
import VerticalStripLLT.Components.DiagramProof.Restriction.CoreExtension

/-! Restriction and extension along an explicitly specified induced subdiagram. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {E : Diagram k} {D : Diagram n}

variable (hE : Forward E) (hD : Forward D) (ι : Fin k ↪o Fin n)

variable
  (hnatural : ∀ u v,
    (∃ e : Edge E.area, e.tail = u ∧ e.head = v) ↔
      ∃ f : Edge D.area, f.tail = ι u ∧ f.head = ι v)
  (hstrict : ∀ u v,
    (∃ e ∈ E.strict, e.tail = u ∧ e.head = v) ↔
      ∃ f ∈ D.strict, f.tail = ι u ∧ f.head = ι v)

/-- Restrict an ambient orientation to the selected relation on the image. -/
def inducedRestrict (θ : Orientation D) : Orientation E :=
  ofSelectedRelation hE
    (fun u v => D.edgeData.selected θ.val (ι u) (ι v))
    (by
      intro u v huv
      obtain ⟨f, hf, ht, hh⟩ := huv
      exact (hnatural u v).mpr ⟨f, ht, hh⟩)
    (by
      intro e he
      obtain ⟨f, hf, ht, hh⟩ :=
        (hstrict e.tail e.head).mp ⟨e, he, rfl, rfl⟩
      have hsel : D.edgeData.selected θ.val f.tail f.head := by
        apply (mem_fullSelection_iff_selected θ f).mp
        exact Finset.mem_union_left _ hf
      simpa only [ht, hh] using hsel)

/-- The restricted state selects exactly the image pairs selected by `θ`. -/
@[simp]
theorem inducedRestrict_selected (θ : Orientation D) (u v : Fin k) :
    E.edgeData.selected (inducedRestrict hE ι hnatural hstrict θ).val u v ↔
      D.edgeData.selected θ.val (ι u) (ι v) :=
  selected_ofSelectedRelation ..

/-- Extend a restricted state while retaining every selected exterior relation. -/
def inducedExtend (θ : Orientation D) (α : Orientation E) : Orientation D :=
  ofSelectedRelation hD
    (fun u v =>
      (∃ a b, ι a = u ∧ ι b = v ∧ E.edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ D.edgeData.selected θ.val u v))
    (by
      intro u v huv
      rcases huv with ⟨a, b, ha, hb, hab⟩ | ⟨_, huv⟩
      · obtain ⟨e, ht, hh⟩ :=
          (hnatural a b).mp (by
            obtain ⟨e, _, ht, hh⟩ := hab
            exact ⟨e, ht, hh⟩)
        exact ⟨e, ha ▸ ht, hb ▸ hh⟩
      · obtain ⟨e, _, ht, hh⟩ := huv
        exact ⟨e, ht, hh⟩)
    (by
      intro e he
      by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
      · obtain ⟨a, b, ha, hb⟩ := hcore
        obtain ⟨f, hf, hfa, hfb⟩ :=
          (hstrict a b).mpr ⟨e, he, ha.symm, hb.symm⟩
        left
        exact ⟨a, b, ha, hb,
          ⟨f, Finset.mem_union_left _ hf, hfa, hfb⟩⟩
      · right
        exact ⟨hcore, (mem_fullSelection_iff_selected θ e).mp
          (Finset.mem_union_left _ he)⟩)

@[simp]
theorem inducedExtend_selected (θ : Orientation D) (α : Orientation E) (u v : Fin n) :
    D.edgeData.selected (inducedExtend hD ι hnatural hstrict θ α).val u v ↔
      (∃ a b, ι a = u ∧ ι b = v ∧ E.edgeData.selected α.val a b) ∨
      ((¬ ∃ a b, ι a = u ∧ ι b = v) ∧ D.edgeData.selected θ.val u v) :=
  selected_ofSelectedRelation ..

@[simp]
theorem inducedExtend_inside (θ : Orientation D) (α : Orientation E) (u v : Fin k) :
    D.edgeData.selected (inducedExtend hD ι hnatural hstrict θ α).val
        (ι u) (ι v) ↔ E.edgeData.selected α.val u v := by
  rw [inducedExtend_selected]
  simp [ι.injective.eq_iff]

theorem inducedExtend_outside (θ : Orientation D) (α : Orientation E)
    (u v : Fin n) (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
    D.edgeData.selected (inducedExtend hD ι hnatural hstrict θ α).val u v ↔
      D.edgeData.selected θ.val u v := by
  rw [inducedExtend_selected]
  have hno : ¬ ∃ a b, ι a = u ∧ ι b = v ∧ E.edgeData.selected α.val a b := by
    rintro ⟨a, b, ha, hb, _⟩
    exact hout ⟨a, b, ha, hb⟩
  simp only [hno, hout, not_false_eq_true, true_and, false_or]

@[simp]
theorem inducedExtend_restrict (θ : Orientation D) :
    inducedExtend hD ι hnatural hstrict θ
        (inducedRestrict hE ι hnatural hstrict θ) = θ := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    inducedExtend_selected]
  constructor
  · rintro (⟨a, b, ha, hb, hab⟩ | ⟨_, h⟩)
    · rw [inducedRestrict_selected] at hab
      simpa only [ha, hb] using hab
    · exact h
  · intro he
    by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨a, b, ha, hb⟩ := hcore
      exact Or.inl ⟨a, b, ha, hb, (inducedRestrict_selected hE ι hnatural hstrict θ a b).mpr
        (by simpa only [ha, hb] using he)⟩
    · exact Or.inr ⟨hcore, he⟩

theorem induced_lift_reachable (θ : Orientation D)
    (hcovers : ∀ α u v,
      Cover (inducedExtend hD ι hnatural hstrict θ α) (ι u) (ι v) ↔
        Cover α u v)
    {α : Orientation E}
    (h : Relation.ReflTransGen (Flip E)
      (inducedRestrict hE ι hnatural hstrict θ) α) :
    Relation.ReflTransGen (Flip D) θ
      (inducedExtend hD ι hnatural hstrict θ α) := by
  have hp := CoreExtension.lift_reachable_of_cover_iff hD hE ι
    (inducedExtend hD ι hnatural hstrict θ)
    (inducedExtend_inside hD ι hnatural hstrict θ)
    (fun α β u v hout =>
      (inducedExtend_outside hD ι hnatural hstrict θ α u v hout).trans
        (inducedExtend_outside hD ι hnatural hstrict θ β u v hout).symm)
    hcovers h
  simpa only [inducedExtend_restrict] using hp

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Circular.CornerStrictifyOrientation

/-! Port of the preserved Aristotle corner-reduction candidate; see docs/ARISTOTLE.md. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Diagram

variable {n : ℕ}

noncomputable section

/-- The embedding of edges of the lowered area. -/
def cornerEmb (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    Edge (D.cornerArea e he) ↪ Edge D.area :=
  ⟨D.cornerIncl e he, D.cornerIncl_injective e he⟩

theorem cornerIncl_restrict (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (f : Edge D.area) (hf : f ≠ e) : D.cornerIncl e he (D.cornerRestrict e he f hf) = f := rfl

theorem mem_deleteCorner_strict (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (f : Edge (D.cornerArea e he)) :
    f ∈ (D.deleteCorner e he).strict ↔ D.cornerIncl e he f ∈ D.strict := by
  change f ∈ Finset.univ.filter _ ↔ _
  simp

/-- Selected sets that correspond under the edge embedding. -/
theorem deleteCorner_corr (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (A : Finset (Edge D.area)) (A2 : Finset (Edge (D.cornerArea e he)))
    (heA : e ∉ A) (hA : ∀ f, f ∈ A2 ↔ D.cornerIncl e he f ∈ A) :
    (∀ f ∈ D.strict ∪ A, ∃ g ∈ (D.deleteCorner e he).strict ∪ A2, g.1 = f.1) ∧
      (∀ g ∈ (D.deleteCorner e he).strict ∪ A2, ∃ f ∈ D.strict ∪ A, f.1 = g.1) := by
  constructor
  · intro f hf
    have hfe : f ≠ e := by
      rintro rfl
      rcases Finset.mem_union.mp hf with h | h
      · exact hns h
      · exact heA h
    refine ⟨D.cornerRestrict e he f hfe, ?_, rfl⟩
    rcases Finset.mem_union.mp hf with h | h
    · exact Finset.mem_union_left _ ((D.mem_deleteCorner_strict e he _).mpr h)
    · exact Finset.mem_union_right _ ((hA _).mpr h)
  · intro g hg
    refine ⟨D.cornerIncl e he g, ?_, rfl⟩
    rcases Finset.mem_union.mp hg with h | h
    · exact Finset.mem_union_left _ ((D.mem_deleteCorner_strict e he _).mp h)
    · exact Finset.mem_union_right _ ((hA _).mp h)

/-- Orientations avoiding a non-strict corner are orientations of the smaller diagram. -/
def orientToDelete (D : Diagram n) (e : Edge D.area) (he : IsCorner e) (hns : e ∉ D.strict)
    (θ : Orientation D) (h : e ∉ θ.val) : Orientation (D.deleteCorner e he) :=
  ⟨Finset.univ.filter fun f => D.cornerIncl e he f ∈ θ.val, by
    have hA : ∀ f, f ∈ Finset.univ.filter (fun f => D.cornerIncl e he f ∈ θ.val) ↔
        D.cornerIncl e he f ∈ θ.val := by simp
    constructor
    · intro f hf
      rw [mem_normalEdges_iff, mem_deleteCorner_strict]
      exact (mem_normalEdges_iff D _).mp (θ.property.1 ((hA f).mp hf))
    · obtain ⟨h1, h2⟩ := D.deleteCorner_corr e he hns θ.val _ h hA
      intro v hv
      apply θ.property.2 v
      rw [selected_eq_of θ.val _ h1 h2]
      exact hv⟩

def orientFromDelete (D : Diagram n) (e : Edge D.area) (he : IsCorner e) (hns : e ∉ D.strict)
    (θ : Orientation (D.deleteCorner e he)) : Orientation D :=
  ⟨θ.val.map (D.cornerEmb e he), by
    have heA : e ∉ θ.val.map (D.cornerEmb e he) := by
      simp only [Finset.mem_map]
      rintro ⟨f, _, hf⟩
      exact D.cornerIncl_ne e he f hf
    have hA : ∀ f, f ∈ θ.val ↔ D.cornerIncl e he f ∈ θ.val.map (D.cornerEmb e he) := by
      intro f
      exact (Finset.mem_map' (D.cornerEmb e he)).symm
    constructor
    · intro g hg
      rw [Finset.mem_map] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [mem_normalEdges_iff]
      have := (mem_normalEdges_iff _ f).mp (θ.property.1 hf)
      rw [mem_deleteCorner_strict] at this
      exact this
    · obtain ⟨h1, h2⟩ := D.deleteCorner_corr e he hns _ θ.val heA hA
      intro v hv
      rw [selected_eq_of _ θ.val h1 h2] at hv
      exact θ.property.2 v hv⟩

theorem orientToDelete_val (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (θ : Orientation D) (h : e ∉ θ.val) :
    (D.orientToDelete e he hns θ h).val =
      Finset.univ.filter fun f => D.cornerIncl e he f ∈ θ.val := rfl

theorem orientFromDelete_val (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (θ : Orientation (D.deleteCorner e he)) :
    (D.orientFromDelete e he hns θ).val = θ.val.map (D.cornerEmb e he) := rfl

theorem map_filter_cornerIncl (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (A : Finset (Edge D.area)) (h : e ∉ A) :
    (Finset.univ.filter fun f => D.cornerIncl e he f ∈ A).map (D.cornerEmb e he) = A := by
  ext g
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact hf
  · intro hg
    have hge : g ≠ e := fun h' => h (h' ▸ hg)
    exact ⟨D.cornerRestrict e he g hge, hg, rfl⟩

theorem filter_map_cornerIncl (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (A : Finset (Edge (D.cornerArea e he))) :
    (Finset.univ.filter fun f => D.cornerIncl e he f ∈ A.map (D.cornerEmb e he)) = A := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Finset.mem_map' (D.cornerEmb e he)

/-- The expansion part avoiding the corner. -/
theorem sum_orient_not_mem (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    ∑ θ ∈ Finset.univ.filter (fun θ : Orientation D => e ∉ θ.val),
        MvPolynomial.C (Polynomial.X ^ θ.val.card) * θ.hrvMonomial =
      shiftedOrientationExpansion (D.deleteCorner e he) := by
  rw [shiftedOrientationExpansion]
  refine Finset.sum_bij'
    (fun θ hθ => D.orientToDelete e he hns θ (Finset.mem_filter.mp hθ).2)
    (fun θ _ => D.orientFromDelete e he hns θ)
    (fun θ _ => Finset.mem_univ _)
    (fun θ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [orientFromDelete_val, Finset.mem_map]
      rintro ⟨f, _, hf⟩
      exact D.cornerIncl_ne e he f hf⟩)
    ?_ ?_ ?_
  · intro θ hθ
    apply Subtype.ext
    change (Finset.univ.filter fun f => D.cornerIncl e he f ∈ θ.val).map (D.cornerEmb e he) = _
    exact D.map_filter_cornerIncl e he θ.val (Finset.mem_filter.mp hθ).2
  · intro θ _
    apply Subtype.ext
    change (Finset.univ.filter fun f => D.cornerIncl e he f ∈ θ.val.map (D.cornerEmb e he)) = _
    exact D.filter_map_cornerIncl e he θ.val
  · intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2
    have hA : ∀ f, f ∈ (D.orientToDelete e he hns θ h).val ↔
        D.cornerIncl e he f ∈ θ.val := by
      intro f; rw [orientToDelete_val]; simp
    obtain ⟨h1, h2⟩ := D.deleteCorner_corr e he hns θ.val _ h hA
    have hcard : (D.orientToDelete e he hns θ h).val.card = θ.val.card := by
      rw [← Finset.card_map (D.cornerEmb e he), orientToDelete_val,
        D.map_filter_cornerIncl e he θ.val h]
    rw [Orientation.hrvMonomial_eq_of_hrv θ (D.orientToDelete e he hns θ h)
      (Orientation.hrv_eq_of_liftStep _ _ (liftStep_eq_of θ.val _ h1 h2)), hcard]

/-- The shifted orientation expansion satisfies deletion–contraction at a non-strict corner. -/
theorem shiftedOrientationExpansion_corner (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    shiftedOrientationExpansion D =
      MvPolynomial.C Polynomial.X * shiftedOrientationExpansion (D.strictify e he) +
        shiftedOrientationExpansion (D.deleteCorner e he) := by
  rw [← D.sum_orient_mem e he hns, ← D.sum_orient_not_mem e he hns,
    Finset.sum_filter_add_sum_filter_not]
  rfl

end

end Diagram

end VerticalStripLLT.Circular

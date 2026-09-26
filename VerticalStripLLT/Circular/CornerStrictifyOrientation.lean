import VerticalStripLLT.Circular.CornerDiagram
import VerticalStripLLT.Circular.HRVTransport

/-! Port of the preserved Aristotle corner-reduction candidate; see docs/ARISTOTLE.md. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Diagram

variable {n : ℕ}

noncomputable section

/-- Orientations containing a non-strict corner are orientations with that corner strict. -/
def orientToStrictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (θ : Orientation D) (h : e ∈ θ.val) : Orientation (D.strictify e he) :=
  ⟨θ.val.erase e, by
    constructor
    · intro f hf
      have hfe := Finset.ne_of_mem_erase hf
      have hfθ := Finset.mem_of_mem_erase hf
      have hn := (mem_normalEdges_iff D f).mp (θ.property.1 hfθ)
      rw [mem_normalEdges_iff]
      change f ∉ insert e D.strict
      simp [hfe, hn]
    · have hsel : (D.strictify e he).edgeData.selected (θ.val.erase e) =
          D.edgeData.selected θ.val := by
        change (D.edgeData.withStrict e).selected (θ.val.erase e) = _
        unfold EdgeData.selected
        have : (D.edgeData.withStrict e).strict ∪ θ.val.erase e =
            D.edgeData.strict ∪ θ.val := by
          change insert e D.strict ∪ θ.val.erase e = D.strict ∪ θ.val
          ext f; by_cases hf : f = e
          · subst hf; simp [h]
          · simp [hf]
        rw [this]; rfl
      intro v hv
      rw [hsel] at hv
      exact θ.property.2 v hv⟩

/-- Adding the corner back. -/
def orientFromStrictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (θ : Orientation (D.strictify e he)) : Orientation D :=
  ⟨insert e θ.val, by
    constructor
    · intro f hf
      rw [mem_normalEdges_iff]
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hns
      · have := (mem_normalEdges_iff (D.strictify e he) f).mp (θ.property.1 hf)
        change f ∉ insert e D.strict at this
        exact fun h' => this (Finset.mem_insert_of_mem h')
    · have hsel : D.edgeData.selected (insert e θ.val) =
          (D.strictify e he).edgeData.selected θ.val := by
        change _ = (D.edgeData.withStrict e).selected θ.val
        unfold EdgeData.selected
        have : (D.edgeData.withStrict e).strict ∪ θ.val =
            D.edgeData.strict ∪ insert e θ.val := by
          change insert e D.strict ∪ θ.val = D.strict ∪ insert e θ.val
          ext f; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        rw [this]; rfl
      intro v hv
      rw [hsel] at hv
      exact θ.property.2 v hv⟩

theorem orientToStrictify_val (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (θ : Orientation D) (h : e ∈ θ.val) :
    (D.orientToStrictify e he θ h).val = θ.val.erase e := rfl

theorem orientFromStrictify_val (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (θ : Orientation (D.strictify e he)) :
    (D.orientFromStrictify e he hns θ).val = insert e θ.val := rfl

theorem not_mem_strictify_orient (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (θ : Orientation (D.strictify e he)) : e ∉ θ.val := by
  intro h
  have := (mem_normalEdges_iff (D.strictify e he) e).mp (θ.property.1 h)
  exact this (Finset.mem_insert_self e D.strict)

theorem strictify_union (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (A : Finset (Edge D.area)) (h : e ∈ A) :
    (D.strictify e he).strict ∪ A.erase e = D.strict ∪ A := by
  change insert e D.strict ∪ A.erase e = D.strict ∪ A
  ext f; by_cases hf : f = e
  · subst hf; simp [h]
  · simp [hf]

theorem liftStep_strictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (A : Finset (Edge D.area)) (h : e ∈ A) :
    (D.strictify e he).liftStep (A.erase e) = D.liftStep A := by
  apply liftStep_eq_of
  · intro f hf
    exact ⟨f, by rw [strictify_union D e he A h] at hf; exact hf, rfl⟩
  · intro f hf
    exact ⟨f, by rw [strictify_union D e he A h]; exact hf, rfl⟩

/-- The expansion part with the corner selected. -/
theorem sum_orient_mem (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    ∑ θ ∈ Finset.univ.filter (fun θ : Orientation D => e ∈ θ.val),
        MvPolynomial.C (Polynomial.X ^ θ.val.card) * θ.hrvMonomial =
      MvPolynomial.C Polynomial.X * shiftedOrientationExpansion (D.strictify e he) := by
  rw [shiftedOrientationExpansion, Finset.mul_sum]
  refine Finset.sum_bij'
    (fun θ hθ => D.orientToStrictify e he θ (Finset.mem_filter.mp hθ).2)
    (fun θ _ => D.orientFromStrictify e he hns θ)
    (fun θ _ => Finset.mem_univ _)
    (fun θ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩)
    ?_ ?_ ?_
  · intro θ hθ
    apply Subtype.ext
    change insert e (θ.val.erase e) = θ.val
    exact Finset.insert_erase (Finset.mem_filter.mp hθ).2
  · intro θ _
    apply Subtype.ext
    change (insert e θ.val).erase e = θ.val
    exact Finset.erase_insert (D.not_mem_strictify_orient e he θ)
  · intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2
    have hcard : θ.val.card = (θ.val.erase e).card + 1 := (Finset.card_erase_add_one h).symm
    rw [Orientation.hrvMonomial_eq_of_hrv θ (D.orientToStrictify e he θ h)
      (Orientation.hrv_eq_of_liftStep _ _ (D.liftStep_strictify e he θ.val h).symm)]
    change _ = _ * (MvPolynomial.C (Polynomial.X ^ (θ.val.erase e).card) * _)
    rw [hcard, pow_succ, MvPolynomial.C_mul]
    ring

end

end Diagram

end VerticalStripLLT.Circular

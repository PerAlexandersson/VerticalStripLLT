import VerticalStripLLT.Circular.Flip
import VerticalStripLLT.Circular.ZeroAreaExpansion

/-! Complete component semantics and the full zero-normal component family. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

variable {n : ℕ} {D : Diagram n}

theorem self_mem_flipComponent (θ : Orientation D) : θ ∈ flipComponent D θ := by
  exact mem_flipComponent_iff.mpr Relation.ReflTransGen.refl

theorem flip_reachable_symm {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) :
    Relation.ReflTransGen (Flip D) η θ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.head (flip_symm D hstep)

theorem flipComponent_eq_of_mem {θ η : Orientation D}
    (h : η ∈ flipComponent D θ) : flipComponent D η = flipComponent D θ := by
  have hpath := mem_flipComponent_iff.mp h
  ext ψ
  rw [mem_flipComponent_iff, mem_flipComponent_iff]
  exact ⟨fun hψ => hpath.trans hψ, fun hψ => (flip_reachable_symm hpath).trans hψ⟩

/-- The actual strict order-enumerator sum of the complete global component. -/
noncomputable def componentStrictEnumerator (D : Diagram n) (θ : Orientation D)
    (m : ℕ) : XPoly m :=
  ∑ η ∈ flipComponent D θ, D.edgeData.strictOrderEnumerator η.val m

theorem weighted_componentStrictEnumerator (D : Diagram n) (θ : Orientation D) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
      MvPolynomial.C (Polynomial.X ^ θ.val.card) * componentStrictEnumerator D θ m := by
  rw [componentStrictEnumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [card_eq_of_mem_flipComponent hη]

theorem flipComponent_eq_singleton_of_no_normal
    (hN : D.edgeData.normalEdges = ∅) (θ : Orientation D) :
    flipComponent D θ = {θ} := by
  ext η
  have hη : η = θ := Subtype.ext
    ((η.val_eq_empty_of_no_normal hN).trans (θ.val_eq_empty_of_no_normal hN).symm)
  subst η
  simp [self_mem_flipComponent]

/-- The strict/e component identity for all zero-normal diagrams and all finite alphabets. -/
theorem component_strict_eq_elementary_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  rw [componentStrictEnumerator, componentHRV, flipComponent_eq_singleton_of_no_normal hN]
  simpa using strictOrderEnumerator_eq_eval_hrvMonomial_of_no_normal hN θ m

end VerticalStripLLT.Circular

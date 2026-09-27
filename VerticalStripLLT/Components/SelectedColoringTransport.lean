import VerticalStripLLT.Components.ComponentScalars

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reindexing strict colorings along a selected-relation isomorphism. -/

namespace VerticalStripLLT.Components

open Circular
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D E : Diagram n}

/--
The strict-coloring enumerator depends on an edge instance only through its
selected relation.  The coloring reindexing is `c ↦ c ∘ σ.symm`; the product
monomial is preserved by the corresponding finite product equivalence.
-/
theorem strictOrderEnumerator_selected_relabel
    (θ : Circular.Orientation D) (η : Circular.Orientation E) (σ : Fin n ≃ Fin n)
    (hrel : ∀ i j, E.edgeData.selected η.val i j ↔
      D.edgeData.selected θ.val (σ i) (σ j)) (m : ℕ) :
    E.edgeData.strictOrderEnumerator η.val m =
      D.edgeData.strictOrderEnumerator θ.val m := by
  classical
  rw [E.edgeData.strictOrderEnumerator_eq_selected_sum,
    D.edgeData.strictOrderEnumerator_eq_selected_sum]
  let colorEquiv : (Fin n → Fin m) ≃ (Fin n → Fin m) := {
    toFun := fun c => c ∘ σ.symm
    invFun := fun c => c ∘ σ
    left_inv := by
      intro c
      funext v
      simp
    right_inv := by
      intro c
      funext v
      simp
  }
  refine Fintype.sum_equiv colorEquiv _ _ ?_
  intro c
  have hadm :
      (∀ u v, E.edgeData.selected η.val u v → c u < c v) ↔
        (∀ u v, D.edgeData.selected θ.val u v →
          (c ∘ σ.symm) u < (c ∘ σ.symm) v) := by
    constructor
    · intro hc u v huv
      have huv' : E.edgeData.selected η.val (σ.symm u) (σ.symm v) :=
        (hrel (σ.symm u) (σ.symm v)).mpr (by
          simpa only [Equiv.apply_symm_apply] using huv)
      exact hc _ _ huv'
    · intro hc u v huv
      have huv' : D.edgeData.selected θ.val (σ u) (σ v) :=
        (hrel u v).mp huv
      have h := hc (σ u) (σ v) huv'
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  have hprod :
      (∏ v, (MvPolynomial.X ((c ∘ σ.symm) v) : XPoly m)) =
        ∏ v, (MvPolynomial.X (c v) : XPoly m) := by
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ.symm
        (fun v => (MvPolynomial.X (c v) : XPoly m)))
  dsimp [colorEquiv, EdgeData.monomial]
  split_ifs with hE hD hD
  · exact hprod.symm
  · exact (hD (hadm.mp hE)).elim
  · exact (hE (hadm.mpr hD)).elim
  · rfl

end

end VerticalStripLLT.Components

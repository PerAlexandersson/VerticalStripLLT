import VerticalStripLLT.Circular.AliasReductionOrient

/-! Transport of restricted orientation sums by general periodic relabelings. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} {D Q : Diagram n}

variable (π : Fin n ≃ Fin n) (σ : ℤ ≃ ℤ)
  (R : Finset (Fin n × Fin n))


variable (hR : R ⊆ D.pairGraph.normalEdges)
  (hR' : R.map ((Equiv.prodCongr π π).toEmbedding) ⊆ Q.pairGraph.normalEdges)
  (hres : ∀ x, Q.residue (σ x) = π (D.residue x))
  (hstep : ∀ (A : Finset (Fin n × Fin n)), A ⊆ R → ∀ x y,
    D.liftStep (D.edgesOfPairs A) x y ↔
      Q.liftStep (Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding))) (σ x) (σ y))
  (horder : ∀ (A : Finset (Fin n × Fin n)), A ⊆ R → ∀ x y,
    (∀ z, ¬ D.liftStep (D.edgesOfPairs A) x z) →
    (∀ z, ¬ D.liftStep (D.edgesOfPairs A) y z) → x ≤ y →
    σ x ≤ σ y)

include hres hstep

/-- Admissibility is preserved by the integer and finite relabeling. -/
theorem pairset_admissible_conjugate (A : Finset (Fin n × Fin n)) (hA : A ⊆ R) :
    D.edgeData.Admissible (D.edgesOfPairs A) ↔
      Q.edgeData.Admissible (Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding))) := by
  rw [D.admissible_iff_lift, Q.admissible_iff_lift]
  have hfwd : ∀ {x y : ℤ},
      Relation.TransGen (D.liftStep (D.edgesOfPairs A)) x y →
      Relation.TransGen
        (Q.liftStep (Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding))))
        (σ x) (σ y) := by
    intro x y h
    exact Relation.TransGen.lift σ
      (fun u v huv => (hstep A hA u v).mp huv) _ _ h
  have hbwd : ∀ {x y : ℤ},
      Relation.TransGen
        (Q.liftStep (Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding)))) x y →
      Relation.TransGen (D.liftStep (D.edgesOfPairs A)) (σ.symm x) (σ.symm y) := by
    intro x y h
    exact Relation.TransGen.lift σ.symm
      (fun u v huv => (hstep A hA (σ.symm u) (σ.symm v)).mpr (by simpa using huv))
      _ _ h
  constructor
  · intro h z w hz
    have hz' := h (σ.symm z) (σ.symm w) (hbwd hz)
    intro heq
    apply hz'
    apply π.injective
    rw [← hres (σ.symm z), ← hres (σ.symm w)]
    simpa using heq
  · intro h z w hz
    have hz' := h (σ z) (σ w) (hfwd hz)
    intro heq
    apply hz'
    rw [hres, hres]
    exact congrArg π heq

include hR hR' horder in
/-- Orientation monomials agree under the relabeling. -/
theorem orientMono_conjugate (A : Finset (Fin n × Fin n)) (hA : A ⊆ R) :
    D.orientMono (D.edgesOfPairs A) =
      Q.orientMono (Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding))) := by
  have hA' : A.map ((Equiv.prodCongr π π).toEmbedding) ⊆ Q.pairGraph.normalEdges :=
    (Finset.map_subset_map.mpr hA).trans hR'
  apply D.orientMono_eq_of _ _ (D.edgesOfPairs_sub_normal (hA.trans hR))
    (Q.edgesOfPairs_sub_normal hA')
  · intro ha
    have ha' := (pairset_admissible_conjugate π σ R hres hstep A hA).mp ha
    refine ⟨ha', fun ha'' => ?_⟩
    let θ : Orientation D :=
      ⟨D.edgesOfPairs A, D.edgesOfPairs_sub_normal (hA.trans hR), ha⟩
    let η : Orientation Q :=
      ⟨Q.edgesOfPairs (A.map ((Equiv.prodCongr π π).toEmbedding)),
        Q.edgesOfPairs_sub_normal hA', ha''⟩
    apply Orientation.hrvMonomial_conjugate θ η π
    apply Orientation.hrv_conjugate θ η σ π hres
    · intro x y
      exact hstep A hA x y
    · exact horder A hA
  · intro ha'
    exact (pairset_admissible_conjugate π σ R hres hstep A hA).mpr ha'

include hR hR' horder in
/-- Restricted orientation sums are invariant under the relabeling. -/
theorem orientSum_conjugate :
    D.orientSum (D.edgesOfPairs R) =
      Q.orientSum (Q.edgesOfPairs (R.map ((Equiv.prodCongr π π).toEmbedding))) := by
  rw [D.orientSum_edgesOfPairs hR, Q.orientSum_edgesOfPairs hR']
  apply Finset.sum_nbij' (fun A => A.map ((Equiv.prodCongr π π).toEmbedding))
    (fun U => U.map (Equiv.prodCongr π π).symm.toEmbedding)
  · intro A hA
    rw [Finset.mem_powerset] at hA ⊢
    exact Finset.map_subset_map.mpr hA
  · intro A hA
    rw [Finset.mem_powerset] at hA ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp (hA hy)
    obtain ⟨a, b⟩ := z
    simpa using hz
  · intro U hU
    ext ⟨a, b⟩
    simp
  · intro A hA
    ext ⟨a, b⟩
    simp
  · intro A hA
    rw [Finset.card_map]
    rw [D.orientMono_conjugate π σ R hR hR' hres hstep horder A
      (Finset.mem_powerset.mp hA)]

end Diagram
end VerticalStripLLT.Circular

import VerticalStripLLT.Circular.ChainSingletonData

/-! Reindexing colorings of a strict chain with one isolated vertex. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace ChainSingletonData

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

noncomputable def coloringEquiv (m : ℕ) :
    (Fin n → Fin m) ≃ (Fin m × (Fin (k + 1) → Fin m)) where
  toFun c := (c S.isolated, fun i => c (S.chain i))
  invFun p v := (S.vertices.symm v).elim (fun i => p.2 i) (fun _ => p.1)
  left_inv c := by
    funext v
    obtain ⟨u, rfl⟩ := S.vertices.surjective v
    cases u <;> simp [chain, isolated]
  right_inv p := by
    apply Prod.ext
    · simp [isolated]
    · funext i
      simp [chain]

@[simp] theorem coloringEquiv_apply_isolated (m : ℕ) (c : Fin n → Fin m) :
    (S.coloringEquiv m c).1 = c S.isolated := rfl

@[simp] theorem coloringEquiv_apply_chain (m : ℕ) (c : Fin n → Fin m)
    (i : Fin (k + 1)) : (S.coloringEquiv m c).2 i = c (S.chain i) := rfl

@[simp] theorem coloringEquiv_symm_isolated (m : ℕ)
    (p : Fin m × (Fin (k + 1) → Fin m)) :
    (S.coloringEquiv m).symm p S.isolated = p.1 := by
  simp [coloringEquiv, isolated]

@[simp] theorem coloringEquiv_symm_chain (m : ℕ)
    (p : Fin m × (Fin (k + 1) → Fin m)) (i : Fin (k + 1)) :
    (S.coloringEquiv m).symm p (S.chain i) = p.2 i := by
  simp [coloringEquiv, chain]

theorem monomial_coloringEquiv_symm (m : ℕ)
    (p : Fin m × (Fin (k + 1) → Fin m)) :
    EdgeData.monomial ((S.coloringEquiv m).symm p) =
      MvPolynomial.X p.1 * ∏ i, MvPolynomial.X (p.2 i) := by
  unfold EdgeData.monomial
  rw [← S.vertices.prod_comp
    (fun v => (MvPolynomial.X (((S.coloringEquiv m).symm p) v) : XPoly m))]
  rw [Fintype.prod_sum_type]
  simp [coloringEquiv, mul_comm]

theorem coloringLLT_reindex (m : ℕ) :
    D.coloringLLT m = ∑ z : Fin m, ∑ c : Fin (k + 1) → Fin m,
      if StrictMono c then
        MvPolynomial.C (Polynomial.X ^
          (D.edgeData.ascentEdges ((S.coloringEquiv m).symm (z, c))).card) *
          (MvPolynomial.X z * ∏ i, MvPolynomial.X (c i))
      else 0 := by
  unfold Diagram.coloringLLT EdgeData.coloringLLT
  trans ∑ p : Fin m × (Fin (k + 1) → Fin m),
    D.edgeData.coloringWeight ((S.coloringEquiv m).symm p)
  · refine Fintype.sum_equiv (S.coloringEquiv m) _ _ ?_
    intro c
    simp
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro c _
  rw [EdgeData.coloringWeight, S.admissibleColoring_iff,
    S.monomial_coloringEquiv_symm]
  simp only [S.coloringEquiv_symm_chain]

end ChainSingletonData
end VerticalStripLLT.Circular

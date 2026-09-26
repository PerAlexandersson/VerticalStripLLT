import VerticalStripLLT.Circular.RootedChainCertificate
import VerticalStripLLT.Circular.HRVEvaluation
import VerticalStripLLT.Circular.ZeroAreaSemantics

/-! The entire circular zero non-strict area expansion, in every finite alphabet. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

variable {n : ℕ} {D : Diagram n}

set_option backward.isDefEq.respectTransparency false in
theorem strictOrderEnumerator_eq_eval_hrvMonomial_of_no_normal
    (hN : D.edgeData.normalEdges = ∅) (θ : Orientation D) (m : ℕ) :
    D.edgeData.strictOrderEnumerator θ.val m = evalElementary m θ.hrvMonomial := by
  let C := rootedChainColoringCertificate (D.edgeData.selected θ.val) θ.hrv
    θ.property.2
    (fun u v h => θ.hrv_eq_of_selected_of_no_normal hN h)
    (fun u v h => θ.same_hrv_comparable_of_no_normal hN h)
  have hsum := rooted_chain_coloring_sum_eq_prod_esymm
    (D.edgeData.selected θ.val) θ.hrv C m
  rw [θ.evalElementary_hrvMonomial m]
  calc
    D.edgeData.strictOrderEnumerator θ.val m =
        ∑ c : Fin n → Fin m,
          if ∀ u v, D.edgeData.selected θ.val u v → c u < c v then
            ∏ u, MvPolynomial.X (c u) else 0 := by
      unfold EdgeData.strictOrderEnumerator EdgeData.monomial
      apply Finset.sum_congr rfl
      intro c _
      have hc : (∀ e ∈ D.strict ∪ θ.val, c e.tail < c e.head) ↔
          ∀ u v, D.edgeData.selected θ.val u v → c u < c v := by
        constructor
        · intro he u v huv
          exact D.edgeData.lt_of_selected θ.val c he huv
        · intro he e he_mem
          exact he e.tail e.head ⟨e, he_mem, rfl, rfl⟩
      exact ite_congr (propext hc) (fun _ => rfl) (fun _ => rfl)
    _ = ∏ r : Fin n, MvPolynomial.esymm (Fin m) Q
        (Fintype.card {u : Fin n // θ.hrv u = r}) := by
      convert hsum using 1
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro r _
      congr 1
      exact Fintype.card_subtype _

/-- No recurrence, decomposition, or HRV identity is assumed in this general base family. -/
theorem coloringLLT_shifted_eq_expansion_of_no_normal (D : Diagram n)
    (hN : D.edgeData.normalEdges = ∅) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  by_cases hθ : Nonempty (Orientation D)
  · let θ : Orientation D := Classical.choice hθ
    rw [shiftedOrientationExpansion_of_no_normal D hN θ,
      Diagram.coloringLLT, D.edgeData.xQShift_coloringLLT_of_no_normal hN]
    have h := strictOrderEnumerator_eq_eval_hrvMonomial_of_no_normal hN θ m
    rwa [θ.val_eq_empty_of_no_normal hN] at h
  · exact coloringLLT_shifted_eq_expansion_of_no_orientation D hN
      ⟨fun θ => hθ ⟨θ⟩⟩ m

end VerticalStripLLT.Circular

import VerticalStripLLT.Circular.RootedChainCertificate
import VerticalStripLLT.Circular.HRVEvaluation
import VerticalStripLLT.Circular.StrictFibers

/-! Strict-edge orientation expansion when the selected set is empty. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

variable {n : ℕ} {D : Diagram n}

set_option backward.isDefEq.respectTransparency false in
theorem strictOrderEnumerator_eq_eval_hrvMonomial_of_empty
    (θ : Orientation D) (hθ : θ.val = ∅) (m : ℕ) :
    D.edgeData.strictOrderEnumerator θ.val m = evalElementary m θ.hrvMonomial := by
  let C := rootedChainColoringCertificate (D.edgeData.selected θ.val) θ.hrv
    θ.property.2
    (fun u v h => θ.hrv_eq_of_selected_of_empty hθ h)
    (fun u v h => θ.same_hrv_comparable_of_empty hθ h)
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

end VerticalStripLLT.Circular

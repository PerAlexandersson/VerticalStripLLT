import VerticalStripLLT.Circular.EdgeColoring

/-! Strict colorings expressed through the selected relation. -/

namespace VerticalStripLLT.Circular.EdgeData

open scoped BigOperators Classical

variable {V E : Type*}

/-! Rewrite strict admissibility using the selected relation rather than edge
representatives. -/
theorem strictOrderEnumerator_eq_selected_sum
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : EdgeData V E) (A : Finset E) (m : ℕ) :
    G.strictOrderEnumerator A m =
      ∑ c : V → Fin m,
        if ∀ u v, G.selected A u v → c u < c v then
          monomial c else 0 := by
  classical
  unfold EdgeData.strictOrderEnumerator
  apply Finset.sum_congr rfl
  intro c hc
  have hiff :
      (∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e)) ↔
        ∀ u v, G.selected A u v → c u < c v := by
    constructor
    · intro he u v huv
      exact G.lt_of_selected A c he huv
    · intro he e he_mem
      exact he (G.tail e) (G.head e) ⟨e, he_mem, rfl, rfl⟩
  exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)

end VerticalStripLLT.Circular.EdgeData

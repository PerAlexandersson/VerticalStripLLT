import VerticalStripLLT.Circular.GeometricArea
import VerticalStripLLT.Circular.CornerPairs

/-! Area and strict-edge measures for corner deletion and strictification. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped BigOperators Classical

variable {n : ℕ} (D : Diagram n)

theorem deleteCorner_area_sum (e : Edge D.area) (he : IsCorner e) :
    (∑ i, (D.deleteCorner e he).area.area i) + 1 = ∑ i, D.area.area i := by
  have hpos := corner_area_pos he
  have hp (i : Fin n) : (D.deleteCorner e he).area.area i +
      (if i = e.head then 1 else 0) = D.area.area i := by
    change Function.update D.area.area e.head (D.area.area e.head - 1) i + _ = _
    by_cases hi : i = e.head
    · subst i
      simp only [Function.update_self, ↓reduceIte]
      lia
    · rw [Function.update_of_ne hi]
      simp only [hi, ↓reduceIte, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hp i)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] using hs

theorem deleteCorner_strict_card (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    (D.deleteCorner e he).strict.card = D.strict.card := by
  let Q := D.deleteCorner e he
  have hnot : (e.tail, e.head) ∉ D.pairGraph.strictEdges := by
    intro hp
    obtain ⟨f, hf, hpair⟩ := (D.mem_pairGraph_strict_iff _).mp hp
    have hfe : f = e := D.endpointEmbedding.injective hpair
    exact hns (hfe ▸ hf)
  have hcard := congrArg Finset.card (D.deleteCorner_pairGraph_strictEdges e he)
  change Q.pairGraph.strictEdges.card =
    (D.pairGraph.strictEdges.erase (e.tail, e.head)).card at hcard
  rw [Finset.erase_eq_of_notMem hnot] at hcard
  have hQ : Q.pairGraph.strictEdges.card = Q.strict.card := Finset.card_map _
  have hD : D.pairGraph.strictEdges.card = D.strict.card := Finset.card_map _
  rw [hQ, hD] at hcard
  exact hcard

theorem deleteCorner_doubledArea (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    (D.deleteCorner e he).doubledArea + 2 = D.doubledArea := by
  let Q := D.deleteCorner e he
  have hs := D.deleteCorner_area_sum e he
  have hc := D.deleteCorner_strict_card e he hns
  have hbound := Q.strict_card_le_area_sum
  unfold doubledArea
  change 2 * (∑ i, Q.area.area i) - Q.strict.card + 2 =
    2 * (∑ i, D.area.area i) - D.strict.card
  change (∑ i, Q.area.area i) + 1 = ∑ i, D.area.area i at hs
  change Q.strict.card = D.strict.card at hc
  lia

theorem strictify_strict_card (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    (D.strictify e he).strict.card = D.strict.card + 1 := by
  simp [strictify, Finset.card_insert_of_notMem, hns]

theorem strictify_area_sum (e : Edge D.area) (he : IsCorner e) :
    (∑ i, (D.strictify e he).area.area i) = ∑ i, D.area.area i := by
  rfl

theorem strictify_doubledArea (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    (D.strictify e he).doubledArea + 1 = D.doubledArea := by
  let Q := D.strictify e he
  have hc := D.strictify_strict_card e he hns
  unfold doubledArea
  change 2 * (∑ i, Q.area.area i) - Q.strict.card + 1 =
    2 * (∑ i, D.area.area i) - D.strict.card
  have hs : (∑ i, Q.area.area i) = ∑ i, D.area.area i := by
    exact D.strictify_area_sum e he
  change Q.strict.card = D.strict.card + 1 at hc
  have hbound := Q.strict_card_le_area_sum
  lia

end Diagram
end VerticalStripLLT.Circular

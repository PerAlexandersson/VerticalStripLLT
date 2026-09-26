import VerticalStripLLT.Circular.AliasTargetPairs
import VerticalStripLLT.Circular.GeometricArea

/-! Area and strict-card measures for the overlapping ND target. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped BigOperators Classical

variable {n : ℕ} (D : Diagram n)
  (i : Fin n) (f : Edge D.area) (hf : f ∈ D.strict)
  (hi : D.area.next i = f.head)
  (harea : D.area.area f.head = D.area.area i + 1)
  (hlen : 3 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

theorem aliasTarget_strict_card (hheads : ∀ g ∈ D.strict, g.head ≠ i) :
    (D.aliasTarget i f hf hi harea hlen hgap hheads).strict.card = D.strict.card := by
  let Q := D.aliasTarget i f hf hi harea hlen hgap hheads
  let oldPair := (f.tail, f.head)
  let newPair := (D.area.next f.tail, i)
  have hold : oldPair ∈ D.pairGraph.strictEdges :=
    (D.mem_pairGraph_strict_iff _).mpr ⟨f, hf, rfl⟩
  have hnew : newPair ∉ D.pairGraph.strictEdges := by
    intro hp
    obtain ⟨g, hg, hpair⟩ := (D.mem_pairGraph_strict_iff _).mp hp
    exact hheads g hg (congrArg Prod.snd hpair)
  have hcard := congrArg Finset.card
    (D.aliasTarget_pairGraph_strictEdges i f hf hi harea hlen hgap hheads)
  change Q.pairGraph.strictEdges.card =
    (insert newPair (D.pairGraph.strictEdges.erase oldPair)).card at hcard
  have hnew' : newPair ∉ D.pairGraph.strictEdges.erase oldPair := by
    intro h
    exact hnew (Finset.mem_erase.mp h).2
  rw [Finset.card_insert_of_notMem hnew', Finset.card_erase_of_mem hold] at hcard
  have hQ : Q.pairGraph.strictEdges.card = Q.strict.card := Finset.card_map _
  have hD : D.pairGraph.strictEdges.card = D.strict.card := Finset.card_map _
  rw [hQ, hD] at hcard
  have hpos := Finset.card_pos.mpr ⟨f, hf⟩
  change Q.strict.card = D.strict.card
  lia

theorem aliasTarget_area_sum (hheads : ∀ g ∈ D.strict, g.head ≠ i) :
    (∑ v, (D.aliasTarget i f hf hi harea hlen hgap hheads).area.area v) + 3 =
      ∑ v, D.area.area v := by
  have hc := (D.strict_corner f hf).1
  have hne : f.head ≠ i := by
    intro h
    rw [h] at harea
    lia
  have hp (v : Fin n) :
      D.area.aliasLowerValues i f.head v + (if v = i then 1 else 0) +
        (if v = f.head then 2 else 0) = D.area.area v := by
    by_cases hvi : v = i
    · subst v
      rw [D.area.aliasLowerValues_left]
      simp only [↓reduceIte]
      lia
    · by_cases hvf : v = f.head
      · subst v
        rw [D.area.aliasLowerValues_right i f.head hne]
        simp only [hne, ↓reduceIte]
        lia
      · rw [D.area.aliasLowerValues_other i f.head v hvi hvf]
        simp only [hvi, hvf, ↓reduceIte, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => hp v)
  change (∑ v, D.area.aliasLowerValues i f.head v) + 3 =
    ∑ v, D.area.area v
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hs
  lia

theorem aliasTarget_doubledArea (hheads : ∀ g ∈ D.strict, g.head ≠ i) :
    (D.aliasTarget i f hf hi harea hlen hgap hheads).doubledArea + 6 =
      D.doubledArea := by
  let Q := D.aliasTarget i f hf hi harea hlen hgap hheads
  have hs := D.aliasTarget_area_sum i f hf hi harea hlen hgap hheads
  have hc := D.aliasTarget_strict_card i f hf hi harea hlen hgap hheads
  have hbound := Q.strict_card_le_area_sum
  unfold doubledArea
  change 2 * (∑ v, Q.area.area v) - Q.strict.card + 6 =
    2 * (∑ v, D.area.area v) - D.strict.card
  change (∑ v, Q.area.area v) + 3 = ∑ v, D.area.area v at hs
  change Q.strict.card = D.strict.card at hc
  lia

end Diagram
end VerticalStripLLT.Circular

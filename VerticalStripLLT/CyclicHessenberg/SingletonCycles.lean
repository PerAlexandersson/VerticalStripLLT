import VerticalStripLLT.CyclicHessenberg.PermutationDisplay

/-! A cycle display with as many cycles as vertices is the identity permutation. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

private theorem cycleSourceWord_length_eq_tailSum_add_count
    (B : List (V × List V)) :
    (B.map fun b => b.2.length).sum + B.length = (cycleSourceWord B).length := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    change b.2.length + (B.map fun b => b.2.length).sum + (B.length + 1) =
      b.2.length + 1 + (cycleSourceWord B).length
    lia

private theorem cycleWords_eq_of_empty_tails (B : List (V × List V))
    (h : ∀ b ∈ B, b.2 = []) : cycleSourceWord B = cycleTargetWord B := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    have hb := h b (by simp)
    have hB : ∀ c ∈ B, c.2 = [] := by
      intro c hc
      exact h c (by simp [hc])
    simp [cycleSourceWord, cycleTargetWord, hb, ih hB]

namespace CycleDisplay

/-- If every cycle is a singleton, the display permutation is the identity. -/
theorem fullPerm_eq_one_of_count_eq_card {k : ℕ}
    (D : CycleDisplay (Finset.univ : Finset (Fin k))) (hc : D.count = k) :
    D.fullPerm = 1 := by
  have hsource : (cycleSourceWord D.blocks).length = k := by
    calc
      _ = (Finset.univ : Finset (Fin k)).card := D.source_order.length
      _ = k := by simp
  have hsum : (D.blocks.map fun b => b.2.length).sum = 0 := by
    have hlen := cycleSourceWord_length_eq_tailSum_add_count D.blocks
    rw [hsource] at hlen
    change (D.blocks.map fun b => b.2.length).sum + D.count = k at hlen
    rw [hc] at hlen
    lia
  have htails : ∀ b ∈ D.blocks, b.2 = [] := by
    intro b hb
    have hzero := List.all_zero_of_le_zero_le_of_sum_eq_zero
      (l := D.blocks.map fun b => b.2.length)
      (by intro x hx; exact Nat.zero_le x) hsum
      (List.mem_map.mpr ⟨b, hb, rfl⟩)
    exact List.length_eq_zero.mp hzero
  have hwords : D.source.val = D.target.val := by
    exact cycleWords_eq_of_empty_tails D.blocks htails
  apply D.fullPerm_eq_of_map_source 1
  rw [hwords]
  simp

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg

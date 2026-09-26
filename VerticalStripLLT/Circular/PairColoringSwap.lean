import VerticalStripLLT.Circular.PairColoring
import VerticalStripLLT.SwapSum
import Mathlib.Tactic.Ring

/-! Swap invariance for pair-graph coloring weights. -/

namespace VerticalStripLLT.Circular.PairGraph

open scoped BigOperators

theorem card_filter_swapColors {n m : ℕ} (a b : Fin n) (S : Finset (Fin n × Fin n))
    (hS : S.map (swapVertexPair a b) = S) (c : Fin n → Fin m) :
    (S.filter fun e => swapColors a b c e.1 < swapColors a b c e.2).card =
      (S.filter fun e => c e.1 < c e.2).card := by
  conv_rhs => rw [← hS]
  rw [Finset.filter_map, Finset.card_map]
  exact congrArg Finset.card (Finset.filter_congr fun e _ => Iff.rfl)

theorem admissible_swapColors_iff {n m : ℕ} (G : PairGraph n) (a b : Fin n)
    (hs : G.strictEdges.map (swapVertexPair a b) = G.strictEdges) (c : Fin n → Fin m) :
    admissible G (swapColors a b c) ↔ admissible G c := by
  constructor
  · intro h e he
    have hmem := mem_of_map_swapVertexPair_eq a b hs he
    have hlt := h _ hmem
    simpa [swapVertexPair_apply, swapColors] using hlt
  · intro h e he
    have hmem := mem_of_map_swapVertexPair_eq a b hs he
    have hlt := h _ hmem
    simpa [swapVertexPair_apply, swapColors] using hlt

theorem ascentCount_eq_swapColors_add_one {n m : ℕ} (G : PairGraph n) (a b : Fin n)
    (he : (a, b) ∈ G.normalEdges)
    (hn : (G.normalEdges.erase (a, b)).map (swapVertexPair a b) =
      G.normalEdges.erase (a, b))
    (c : Fin n → Fin m) (hc : c a < c b) :
    ascentCount G c = ascentCount G (swapColors a b c) + 1 := by
  unfold ascentCount
  rw [← Finset.insert_erase he]
  have hnot : (a, b) ∉ G.normalEdges.erase (a, b) := Finset.notMem_erase _ _
  rw [Finset.filter_insert, Finset.filter_insert, ite_eq_left hc]
  have hc' : ¬ (swapColors a b c (a, b).1 < swapColors a b c (a, b).2) := by
    simp only [swapColors_apply_left, swapColors_apply_right]
    exact not_lt.mpr hc.le
  rw [ite_eq_right hc', Finset.card_insert_of_notMem (fun h => hnot (Finset.mem_filter.1 h).1),
    card_filter_swapColors a b _ hn c]

theorem coloringWeight_eq_C_X_mul_swapColors {n m : ℕ} (G : PairGraph n) (a b : Fin n)
    (he : (a, b) ∈ G.normalEdges)
    (hs : G.strictEdges.map (swapVertexPair a b) = G.strictEdges)
    (hn : (G.normalEdges.erase (a, b)).map (swapVertexPair a b) =
      G.normalEdges.erase (a, b))
    (c : Fin n → Fin m) (hc : c a < c b) :
    coloringWeight G c = MvPolynomial.C Polynomial.X * coloringWeight G (swapColors a b c) := by
  classical
  unfold coloringWeight
  have hadm := admissible_swapColors_iff G a b hs c
  by_cases h : admissible G c
  · rw [ite_eq_left h, ite_eq_left (hadm.2 h),
      ascentCount_eq_swapColors_add_one G a b he hn c hc,
      prod_X_swapColors, pow_succ, MvPolynomial.C_mul]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hadm.1 h')), mul_zero]

end VerticalStripLLT.Circular.PairGraph

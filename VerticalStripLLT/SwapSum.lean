import VerticalStripLLT.ColoringSwap
import VerticalStripLLT.PathInvariants
import Mathlib.Tactic.Ring

namespace VerticalStripLLT
open scoped BigOperators

def swapVertexPair {n : ℕ} (a b : Fin n) : (Fin n × Fin n) ↪ (Fin n × Fin n) :=
  (Equiv.prodCongr (Equiv.swap a b) (Equiv.swap a b)).toEmbedding

theorem swapVertexPair_apply {n : ℕ} (a b : Fin n) (e : Fin n × Fin n) :
    swapVertexPair a b e = (Equiv.swap a b e.1, Equiv.swap a b e.2) := rfl

theorem mem_of_map_swapVertexPair_eq {n : ℕ} (a b : Fin n) {S : Finset (Fin n × Fin n)}
    (hS : S.map (swapVertexPair a b) = S) {e : Fin n × Fin n} (he : e ∈ S) :
    swapVertexPair a b e ∈ S := by
  rw [← hS]
  exact Finset.mem_map_of_mem _ he

/-- Counting color ascents on a swap-invariant edge set is invariant under swapping colors. -/
theorem card_filter_swapColors {n m : ℕ} (a b : Fin n) (S : Finset (Fin n × Fin n))
    (hS : S.map (swapVertexPair a b) = S) (c : Fin n → Fin m) :
    (S.filter fun e => swapColors a b c e.1 < swapColors a b c e.2).card =
      (S.filter fun e => c e.1 < c e.2).card := by
  conv_rhs => rw [← hS]
  rw [Finset.filter_map, Finset.card_map]
  exact congrArg Finset.card (Finset.filter_congr fun e _ => Iff.rfl)

/-- Admissibility is invariant under swapping colors when strict edges are swap-invariant. -/
theorem admissible_swapColors_iff {n m : ℕ} (P : SchroderPath n) (a b : Fin n)
    (hs : P.strictEdges.map (swapVertexPair a b) = P.strictEdges) (c : Fin n → Fin m) :
    admissible P (swapColors a b c) ↔ admissible P c := by
  constructor
  · intro h e he
    have := h _ (mem_of_map_swapVertexPair_eq a b hs he)
    simpa [swapVertexPair_apply, swapColors] using this
  · intro h e he
    have := h _ (mem_of_map_swapVertexPair_eq a b hs he)
    simpa [swapVertexPair_apply, swapColors] using this

theorem ascentCount_eq_swapColors_add_one {n m : ℕ} (P : SchroderPath n) (a b : Fin n)
    (he : (a,b) ∈ P.normalEdges)
    (hn : (P.normalEdges.erase (a,b)).map (swapVertexPair a b) =
      P.normalEdges.erase (a,b))
    (c : Fin n → Fin m) (hc : c a < c b) :
    ascentCount P c = ascentCount P (swapColors a b c) + 1 := by
  unfold ascentCount
  rw [← Finset.insert_erase he]
  have hnot : (a,b) ∉ P.normalEdges.erase (a,b) := Finset.notMem_erase _ _
  rw [Finset.filter_insert, Finset.filter_insert, ite_eq_left hc]
  have hc' : ¬ (swapColors a b c (a,b).1 < swapColors a b c (a,b).2) := by
    simp only [swapColors_apply_left, swapColors_apply_right]
    exact not_lt.mpr hc.le
  rw [ite_eq_right hc', Finset.card_insert_of_notMem (fun h => hnot (Finset.mem_filter.1 h).1),
    card_filter_swapColors a b _ hn c]

theorem coloringWeight_eq_C_X_mul_swapColors {n m : ℕ} (P : SchroderPath n) (a b : Fin n)
    (he : (a,b) ∈ P.normalEdges)
    (hs : P.strictEdges.map (swapVertexPair a b) = P.strictEdges)
    (hn : (P.normalEdges.erase (a,b)).map (swapVertexPair a b) =
      P.normalEdges.erase (a,b))
    (c : Fin n → Fin m) (hc : c a < c b) :
    coloringWeight P c = MvPolynomial.C Polynomial.X * coloringWeight P (swapColors a b c) := by
  classical
  unfold coloringWeight
  have hadm := admissible_swapColors_iff P a b hs c
  by_cases h : admissible P c
  · rw [ite_eq_left h, ite_eq_left (hadm.2 h),
      ascentCount_eq_swapColors_add_one P a b he hn c hc,
      prod_X_swapColors, pow_succ, MvPolynomial.C_mul]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hadm.1 h')), mul_zero]

theorem coloringLLT_swap_sum {n m : ℕ} (P : SchroderPath n) (a b : Fin n)
    (he : (a,b) ∈ P.normalEdges)
    (hs : P.strictEdges.map (swapVertexPair a b) = P.strictEdges)
    (hn : (P.normalEdges.erase (a,b)).map (swapVertexPair a b) =
      P.normalEdges.erase (a,b)) :
    (∑ c : Fin n → Fin m, if c a < c b then coloringWeight P c else 0) =
      MvPolynomial.C Polynomial.X *
        ∑ c : Fin n → Fin m, if c b < c a then coloringWeight P c else 0 := by
  have hstep : (∑ c : Fin n → Fin m, if c a < c b then coloringWeight P c else 0) =
      ∑ c : Fin n → Fin m, MvPolynomial.C Polynomial.X *
        (if c a < c b then coloringWeight P (swapColors a b c) else 0) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · exact coloringWeight_eq_C_X_mul_swapColors P a b he hs hn c hc
    · rw [mul_zero]
  rw [hstep, ← Finset.mul_sum]
  congr 1
  let swapEquiv : (Fin n → Fin m) ≃ (Fin n → Fin m) :=
    Function.Involutive.toPerm (swapColors a b) (swapColors_involutive a b)
  rw [← Equiv.sum_comp swapEquiv (fun d => if d b < d a then coloringWeight P d else 0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (if c a < c b then coloringWeight P (swapColors a b c) else 0) =
    if swapColors a b c b < swapColors a b c a then
      coloringWeight P (swapColors a b c) else 0
  simp only [swapColors_apply_left, swapColors_apply_right]

end VerticalStripLLT

import VerticalStripLLT.Circular.FirstBounceOrientationMatching
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

include hsame hright in
theorem nn_normal_eq :
    D.edgeData.normalEdges = insert (D.shortenedOldEdge e he hlen)
      (insert (D.bridgeEdge e) (D.baseSet e he hlen)) := by
  ext ε
  simp only [Finset.mem_insert, mem_baseSet_iff, mem_normalEdges_iff]
  constructor
  · intro h
    by_cases h1 : ε = D.shortenedOldEdge e he hlen
    · exact Or.inl h1
    · by_cases h2 : ε = D.bridgeEdge e
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h, h1, h2⟩)
  · rintro (h | h | h)
    · rw [h]; exact D.nn_fE_not_strict e he hlen
    · rw [h]; exact D.nn_bridge_not_strict e hsame hright
    · exact h.1

include hgap hsame hleft hright in
theorem nn_bottom_sum :
    ∑ t ∈ (D.baseSet e he hlen).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
        (D.shortenStrict e he hlen hgap).orientMono (D.targetSet e he hlen hgap t) =
      ∑ t ∈ (D.baseSet e he hlen).powerset,
        MvPolynomial.C (Polynomial.X ^ t.card) * D.orientMono t := by
  symm
  apply Finset.sum_nbij' (D.swapSet e) (D.swapSet e)
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact D.nn_swapSet_subset e he hlen hgap hsame hleft hright t ht
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact D.nn_swapSet_subset e he hlen hgap hsame hleft hright t ht
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact D.nn_swapSet_swapSet e he hlen hgap hsame t ht
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact D.nn_swapSet_swapSet e he hlen hgap hsame t ht
  · intro t ht
    rw [Finset.mem_powerset] at ht
    rw [D.nn_swapSet_card e he hlen hgap hsame t ht,
      D.nn_match_bottom e he hlen hgap hsame hleft hright t ht]

end NN

end Diagram

end VerticalStripLLT.Circular

namespace VerticalStripLLT.Circular.Diagram

theorem shiftedOrientationExpansion_shortenStrict_NN {n : ℕ} (D : Diagram n)
    (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
    (hleft : ¬ D.strictAt (e.tail.val : ℤ))
    (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1)) :
    shiftedOrientationExpansion D =
      MvPolynomial.C (Polynomial.X + 1) *
        shiftedOrientationExpansion (D.shortenStrict e he hlen hgap) := by
  classical
  have hfN : D.shortenedOldEdge e he hlen ∉ insert (D.bridgeEdge e) (D.baseSet e he hlen) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.nn_fE_ne_bridge e he hlen hsame h
    · exact ((D.mem_baseSet_iff e he hlen _).mp h).2.1 rfl
  have hgN : D.bridgeEdge e ∉ D.baseSet e he hlen := fun h =>
    ((D.mem_baseSet_iff e he hlen _).mp h).2.2 rfl
  rw [D.shiftedOrientationExpansion_eq_sum, D.nn_normal_eq e he hlen hsame hright,
    D.nn_target_sum e he hlen hgap hsame hright, Finset.sum_powerset_insert hfN,
    Finset.sum_powerset_insert hgN, Finset.sum_powerset_insert hgN,
    Finset.sum_powerset_insert hgN, D.nn_bottom_sum e he hlen hgap hsame hleft hright,
    mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powerset] at ht
  have hft : D.shortenedOldEdge e he hlen ∉ t := fun h => hfN (Finset.mem_insert_of_mem (ht h))
  have hgt : D.bridgeEdge e ∉ t := fun h => hgN (ht h)
  have hfgt : D.shortenedOldEdge e he hlen ∉ insert (D.bridgeEdge e) t := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact D.nn_fE_ne_bridge e he hlen hsame h
    · exact hft h
  have hid := D.nn_local_identity e he hlen hsame hright t ht
  rw [← D.nn_match_top e he hlen hgap hsame hright t ht]
  rw [Finset.card_insert_of_notMem hgt, Finset.card_insert_of_notMem hft,
    Finset.card_insert_of_notMem hfgt, Finset.card_insert_of_notMem hgt]
  simp only [map_pow, map_add, map_one, pow_succ, map_mul]
  linear_combination (MvPolynomial.C Polynomial.X ^ t.card * MvPolynomial.C Polynomial.X) * hid

end VerticalStripLLT.Circular.Diagram

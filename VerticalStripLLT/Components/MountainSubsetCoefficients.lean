import VerticalStripLLT.Components.MountainCoefficients
import VerticalStripLLT.Components.SubwordSubsets
import Mathlib.Order.Interval.Finset.Nat

/-! Finset reindexing of the ordered mountain coefficient expansion. -/

namespace VerticalStripLLT.Components

open Polynomial

noncomputable section

variable {R : Type*} [Ring R]

private theorem incWord_range_eq_range (n : ℕ) :
    incWord (Finset.range n) = List.range n := by
  simp [incWord]

private theorem decWord_range_eq_reverse_range (n : ℕ) :
    decWord (Finset.range n) = (List.range n).reverse := by
  change (Finset.range n).sort (· ≥ ·) = (List.range n).reverse
  apply List.SortedGT.eq_of_mem_iff
    (Finset.sortedGT_sort _)
    (List.sortedLT_range n).reverse
  intro v
  simp

/-- The polynomial coefficient expansion indexed by two finite subsets. -/
theorem inverseConjugationPolynomial_coeff_powerset_sum (u : ℕ → R) (n k : ℕ) :
    (inverseConjugationPolynomial u n).coeff k =
      ∑ P ∈ (Finset.range n).powerset,
        ∑ T ∈ (Finset.range n).powerset,
          if P.card + T.card = k then
            (-1 : R) ^ P.card *
              (((incWord P).map u).prod * u n * ((decWord T).map u).prod)
          else 0 := by
  classical
  rw [inverseConjugationPolynomial_coeff_subword_sum]
  rw [sum_sublists'_eq_sum_powerset_filter
    (List.range n) (List.nodup_range (n := n))]
  rw [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro P hP
  have hPsub : P ⊆ Finset.range n := Finset.mem_powerset.mp hP
  have hPlen :
      ((List.range n).filter (fun v => decide (v ∈ P))).length = P.card :=
    length_filter_mem_toFinset_eq_card (List.range n) (List.nodup_range (n := n))
      P (by simpa only [List.toFinset_range] using hPsub)
  have hPword :
      (List.range n).filter (fun v => decide (v ∈ P)) = incWord P := by
    rw [← incWord_range_eq_range n]
    exact incWord_filter_mem_eq_incWord _ _ hPsub
  rw [sum_sublists'_eq_sum_powerset_filter
    ((List.range n).reverse) (List.nodup_reverse.mpr (List.nodup_range (n := n)))]
  rw [List.toFinset_reverse, List.toFinset_range]
  apply Finset.sum_congr rfl
  intro T hT
  have hTsub : T ⊆ Finset.range n := Finset.mem_powerset.mp hT
  have hTrev : T ⊆ (List.range n).reverse.toFinset := by
    simpa only [List.toFinset_reverse, List.toFinset_range] using hTsub
  have hTlen :
      (((List.range n).reverse).filter (fun v => decide (v ∈ T))).length = T.card :=
    length_filter_mem_toFinset_eq_card ((List.range n).reverse)
      (List.nodup_reverse.mpr (List.nodup_range (n := n))) T hTrev
  have hTword :
      ((List.range n).reverse).filter (fun v => decide (v ∈ T)) = decWord T := by
    rw [← decWord_range_eq_reverse_range n]
    exact decWord_filter_mem_eq_decWord _ _ hTsub
  rw [hPlen, hPword, hTlen, hTword]

end

end VerticalStripLLT.Components

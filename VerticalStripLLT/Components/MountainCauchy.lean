import VerticalStripLLT.Components.MountainExpansion
import VerticalStripLLT.Components.CauchyStep

/-! The one-peak Cauchy sum in its finite subset form. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {R : Type*} [Ring R]

/-- The finite iterated-commutator peak sum reindexed by its mountain subsets. -/
theorem elementary_adPow_eq_powerset_mountain (u : ℕ → R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) -
        (u j * u k - u k * u j) * u i = 0)
    (xs : List R) :
    (∑ k ∈ Finset.range xs.length,
      elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) =
      ∑ B ∈ (Finset.range n).powerset,
        elementaryScalar xs (B.card + 1) *
          ∑ T ∈ B.powerset,
            (-1 : R) ^ T.card *
              (((incWord (B \ T)).map u).prod * u n *
                ((decWord T).map u).prod) := by
  classical
  let g : Finset ℕ → R := fun B =>
    ∑ T ∈ B.powerset,
      (-1 : R) ^ T.card *
        (((incWord (B \ T)).map u).prod * u n *
          ((decWord T).map u).prod)
  calc
    (∑ k ∈ Finset.range xs.length,
        elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) =
        ∑ k ∈ Finset.range xs.length,
          elementaryScalar xs (k + 1) *
            (∑ B ∈ (Finset.range n).powerset,
              if B.card = k then g B else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [adPow_mountain_expand u squarefree triple n k]
    _ = ∑ B ∈ (Finset.range n).powerset,
          ∑ k ∈ Finset.range xs.length,
            elementaryScalar xs (k + 1) *
              (if B.card = k then g B else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ B ∈ (Finset.range n).powerset,
          elementaryScalar xs (B.card + 1) * g B := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hlt : B.card < xs.length
      · rw [Finset.sum_eq_single B.card]
        · simp
        · intro j hj hne
          simp [hne, eq_comm]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr hlt)).elim
      · have hzero :
            (∑ k ∈ Finset.range xs.length,
              elementaryScalar xs (k + 1) *
                (if B.card = k then g B else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hne : B.card ≠ j := by
            intro heq
            apply hlt
            rw [heq]
            exact Finset.mem_range.mp hj
          simp [hne]
        rw [hzero]
        have hscalar : elementaryScalar xs (B.card + 1) = 0 :=
          elementaryScalar_eq_zero_of_length_lt xs _ (by lia)
        rw [hscalar, zero_mul]
    _ = ∑ B ∈ (Finset.range n).powerset,
          elementaryScalar xs (B.card + 1) *
            ∑ T ∈ B.powerset,
              (-1 : R) ^ T.card *
                (((incWord (B \ T)).map u).prod * u n *
                  ((decWord T).map u).prod) := by
      rfl

end

end VerticalStripLLT.Components

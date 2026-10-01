import VerticalStripLLT.Components.WordProof.CommutatorCoefficients
import VerticalStripLLT.Components.WordProof.MountainSubsetCoefficients
import VerticalStripLLT.Components.WordProof.SquarefreeProducts
import VerticalStripLLT.Components.WordProof.DisjointSubsetSums

/-! The ordered mountain expansion of an iterated commutator. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open Polynomial
open scoped BigOperators
open Classical

noncomputable section

variable {R : Type*} [Ring R]

private def mountainTerm (u : ℕ → R) (n : ℕ)
    (P T : Finset ℕ) : R :=
  ((incWord P).map u).prod * u n * ((decWord T).map u).prod

private theorem negOne_pow_mul_self (m : ℕ) :
    (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    simpa only [pow_succ, mul_neg_one, neg_mul, mul_neg, neg_neg, mul_one] using ih

private theorem mountain_coeff_reindexed (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (n k : ℕ) :
    (∑ P ∈ (Finset.range n).powerset,
      ∑ T ∈ (Finset.range n).powerset,
        if P.card + T.card = k then
          (-1 : R) ^ P.card * mountainTerm u n P T
        else 0) =
      ∑ B ∈ (Finset.range n).powerset,
        ∑ T ∈ B.powerset,
          if B.card = k then
            (-1 : R) ^ (B \ T).card * mountainTerm u n (B \ T) T
          else 0 := by
  let S : Finset ℕ := Finset.range n
  let f : Finset ℕ → Finset ℕ → R := fun P T =>
    if P.card + T.card = k then
      (-1 : R) ^ P.card * mountainTerm u n P T
    else 0
  have hdisj :
      (∑ P ∈ S.powerset, ∑ T ∈ S.powerset,
        f P T) =
        ∑ P ∈ S.powerset, ∑ T ∈ S.powerset,
          if Disjoint P T then f P T else 0 := by
    symm
    apply Finset.sum_congr rfl
    intro P hP
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hPT : Disjoint P T
    · simp [hPT]
    · obtain ⟨a, haP, haT⟩ := Finset.not_disjoint_iff.mp hPT
      have hz : mountainTerm u n P T = 0 := by
        dsimp [mountainTerm]
        have hz' := mountain_product_eq_zero_of_overlap u squarefree
          (incWord P) (decWord T) n ⟨a, ?_, ?_⟩
        · simpa [incWord, decWord] using hz'
        · simpa [incWord] using haP
        · simpa [decWord] using haT
      simp [f, hz]
  have hreindex := sum_powerset_disjoint_eq_union S f
  rw [hdisj, hreindex]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro T hT
  have hTsub : T ⊆ B := Finset.mem_powerset.mp hT
  have hcard : (B \ T).card + T.card = B.card :=
    Finset.card_sdiff_add_card_eq_card hTsub
  simp only [f, hcard]

theorem adPow_mountain_expand (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) -
        (u j * u k - u k * u j) * u i = 0)
    (n k : ℕ) :
    adPow (letterSum u n) (u n) k =
      ∑ B ∈ (Finset.range n).powerset,
        if B.card = k then
          ∑ T ∈ B.powerset,
            (-1 : R) ^ T.card *
              (((incWord (B \ T)).map u).prod * u n *
                ((decWord T).map u).prod)
        else 0 := by
  let S : Finset ℕ := Finset.range n
  let target : R :=
    ∑ B ∈ S.powerset,
      if B.card = k then
        ∑ T ∈ B.powerset,
          (-1 : R) ^ T.card * mountainTerm u n (B \ T) T
      else 0
  have hcoeff := inverseConjugationPolynomial_coeff_powerset_sum u n k
  have hcoeff' := mountain_coeff_reindexed u squarefree n k
  have hscale :
      (-1 : R) ^ k * target =
        ∑ B ∈ S.powerset,
          ∑ T ∈ B.powerset,
            if B.card = k then
              (-1 : R) ^ (B \ T).card * mountainTerm u n (B \ T) T
            else 0 := by
    calc
      (-1 : R) ^ k * target =
          ∑ B ∈ S.powerset,
            (-1 : R) ^ k *
              (if B.card = k then
                ∑ T ∈ B.powerset,
                  (-1 : R) ^ T.card * mountainTerm u n (B \ T) T
              else 0) := by
        simp only [target]
        rw [Finset.mul_sum]
      _ = ∑ B ∈ S.powerset, ∑ T ∈ B.powerset,
            if B.card = k then
              (-1 : R) ^ k *
                ((-1 : R) ^ T.card * mountainTerm u n (B \ T) T)
            else 0 := by
        apply Finset.sum_congr rfl
        intro B hB
        by_cases hk : B.card = k <;> simp [hk, Finset.mul_sum]
      _ = ∑ B ∈ S.powerset, ∑ T ∈ B.powerset,
            if B.card = k then
              (-1 : R) ^ (B \ T).card * mountainTerm u n (B \ T) T
            else 0 := by
        apply Finset.sum_congr rfl
        intro B hB
        apply Finset.sum_congr rfl
        intro T hT
        by_cases hk : B.card = k
        · have hTsub : T ⊆ B := Finset.mem_powerset.mp hT
          have hcard : (B \ T).card + T.card = B.card :=
            Finset.card_sdiff_add_card_eq_card hTsub
          have hsum : (B \ T).card + T.card = k := hcard.trans hk
          have hsign :
              (-1 : R) ^ (B \ T).card =
                (-1 : R) ^ k * (-1 : R) ^ T.card := by
            calc
              (-1 : R) ^ (B \ T).card =
                  (-1 : R) ^ (B \ T).card * 1 := by simp
              _ = (-1 : R) ^ (B \ T).card *
                  ((-1 : R) ^ T.card * (-1 : R) ^ T.card) := by
                rw [negOne_pow_mul_self]
              _ = ((-1 : R) ^ (B \ T).card *
                  (-1 : R) ^ T.card) * (-1 : R) ^ T.card := by
                noncomm_ring
              _ = (-1 : R) ^ k * (-1 : R) ^ T.card := by
                rw [← pow_add, hsum]
          simp only [ite_eq_left hk]
          rw [hsign]
          noncomm_ring
        · simp [hk]
  have hcoeff_ad :
      (inverseConjugationPolynomial u n).coeff k =
        (-1 : R) ^ k * adPow (letterSum u n) (u n) k :=
    inverseConjugationPolynomial_coeff u squarefree triple n k
  have hmain :
      (-1 : R) ^ k * adPow (letterSum u n) (u n) k =
        (-1 : R) ^ k * target := by
    rw [← hcoeff_ad, hcoeff]
    exact hcoeff'.trans hscale.symm
  have hsquare := negOne_pow_mul_self (R := R) k
  calc
    adPow (letterSum u n) (u n) k =
        1 * adPow (letterSum u n) (u n) k := by simp
    _ = ((-1 : R) ^ k * (-1 : R) ^ k) *
        adPow (letterSum u n) (u n) k := by rw [hsquare]
    _ = (-1 : R) ^ k *
        ((-1 : R) ^ k * adPow (letterSum u n) (u n) k) := by
      noncomm_ring
    _ = (-1 : R) ^ k * ((-1 : R) ^ k * target) := by rw [hmain]
    _ = ((-1 : R) ^ k * (-1 : R) ^ k) * target := by
      noncomm_ring
    _ = target := by rw [hsquare, one_mul]

end

end VerticalStripLLT.Components

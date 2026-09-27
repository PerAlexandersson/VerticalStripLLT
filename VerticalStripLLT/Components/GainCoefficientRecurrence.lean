import VerticalStripLLT.Components.GainCoefficient
import VerticalStripLLT.Components.GainContractionExcess
import VerticalStripLLT.Components.RequiredSubsetSums

/-! The actual finite companion coefficient satisfies the signed deletion recurrence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open Classical OrderedPartitions
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq E] (G : GainData V E)

/-- The coefficient identity (**), for every supported `F`, with actual contractions. -/
theorem sum_powerset_coefficient_eq_zero
    (A N F : Finset E) (hFN : F ⊆ A ∪ N) (hAN : Disjoint A N)
    (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hcover : ∀ e ∈ N, e ∈ Nsteps)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card * G.coefficient (A ∪ J) F) = 0 := by
  by_cases hbal : G.Balanced F
  swap
  · simp [G.coefficient_eq_zero_of_not_balanced hbal]
  obtain ⟨p, hp⟩ := hbal
  let H := G.contraction F p
  let cF := weakComponentCount (G.selectedRelation F)
  let J₀ := F ∩ N
  have hrestrict :
      (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card * G.coefficient (A ∪ J) F) =
      ∑ J ∈ (N \ F).powerset,
        (-1 : ℤ) ^ (J₀ ∪ J).card * G.coefficient (A ∪ (J₀ ∪ J)) F := by
    dsimp only [J₀]
    rw [← sum_powerset_required_subset_eq_sdiff_union A N F hFN hAN
      (fun J => (-1 : ℤ) ^ J.card * G.coefficient (A ∪ J) F)]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hFJ : F ⊆ A ∪ J
    · simp only [hFJ, ite_true]
    · simp [hFJ, G.coefficient_eq_zero_of_not_subset hFJ]
  rw [hrestrict]
  have hterm (J : Finset E) (hJ : J ∈ (N \ F).powerset) :
      (-1 : ℤ) ^ (J₀ ∪ J).card * G.coefficient (A ∪ (J₀ ∪ J)) F =
      (-1 : ℤ) ^ (J₀.card + cF) *
        (if H.SimpleCyclesNegative ((A \ F) ∪ J) ∧
            TotallyCyclic (H.selectedRelation ((A \ F) ∪ J))
         then (-1 : ℤ) ^ (J.card + weakComponentCount (H.selectedRelation ((A \ F) ∪ J)))
         else 0) := by
    have hsub : J ⊆ N \ F := Finset.mem_powerset.mp hJ
    have hFX : F ⊆ A ∪ (J₀ ∪ J) := by
      intro e he
      rcases Finset.mem_union.mp (hFN he) with ha | hn
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, hn⟩))
    have hdiff : (A ∪ (J₀ ∪ J)) \ F = (A \ F) ∪ J := by
      ext e
      have h := @hsub e
      simp only [J₀, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h ⊢
      tauto
    have hdisj : Disjoint J₀ J := by
      apply Finset.disjoint_left.mpr
      intro e he₀ heJ
      exact (Finset.mem_sdiff.mp (hsub heJ)).2 (Finset.mem_inter.mp he₀).1
    rw [G.coefficient_eq_contraction hp hFX, hdiff,
      Finset.card_union_of_disjoint hdisj]
    change (-1 : ℤ) ^ (J₀.card + J.card) *
      ((-1 : ℤ) ^ cF * (if H.SimpleCyclesNegative ((A \ F) ∪ J) ∧
        TotallyCyclic (H.selectedRelation ((A \ F) ∪ J))
        then (-1 : ℤ) ^ weakComponentCount (H.selectedRelation ((A \ F) ∪ J)) else 0)) = _
    split_ifs <;> simp only [pow_add] <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hzero := G.contraction_sum_cyclicNegative_eq_zero hp A N P Nsteps
    hN hcover hP hperm hexcess
  change (-1 : ℤ) ^ (J₀.card + cF) * _ = 0
  rw [hzero, mul_zero]

end

end VerticalStripLLT.Components.GainData

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

/-!
# Expansion from finite signed deletion identities

The semantics `W` is arbitrary. A delta base case and matching deletion
identities for `W` and its coefficients imply the expansion by induction on
strict finite subsets. No recursively defined replacement for `W` is used.
-/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {E M : Type*} [DecidableEq E] [AddCommGroup M]

/-- Matching signed deletion identities determine an expansion in fixed ambient terms. -/
theorem eq_sum_coefficient_smul_of_deletion
    (R : Finset E) (W : Finset E → M) (κ : Finset E → Finset E → ℤ)
    (Balanced : Finset E → Prop)
    (hbase : ∀ X, X ⊆ R → Balanced X → ∀ F, F ⊆ R →
      κ X F = if F = X then 1 else 0)
    (hrec : ∀ X, X ⊆ R → ¬Balanced X →
      ∃ N : Finset E, N ⊆ X ∧ N.Nonempty ∧
        (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card • W ((X \ N) ∪ J)) = 0 ∧
        (∀ F, F ⊆ R →
          (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card * κ ((X \ N) ∪ J) F) = 0)) :
    ∀ X, X ⊆ R → W X = ∑ F ∈ R.powerset, κ X F • W F := by
  classical
  let defect : Finset E → M := fun X => W X - ∑ F ∈ R.powerset, κ X F • W F
  have hdefect : ∀ X, X ⊆ R → defect X = 0 := by
    intro X
    refine Finset.strongInductionOn X ?_
    intro X ih hXR
    by_cases hbal : Balanced X
    · have hexpand : (∑ F ∈ R.powerset, κ X F • W F) = W X := by
        calc
          (∑ F ∈ R.powerset, κ X F • W F) =
              ∑ F ∈ R.powerset, (if F = X then (1 : ℤ) else 0) • W F := by
            apply Finset.sum_congr rfl
            intro F hF
            rw [hbase X hXR hbal F (Finset.mem_powerset.mp hF)]
          _ = W X := by
            simp [ite_smul, Finset.mem_powerset, hXR]
      dsimp only [defect]
      rw [hexpand, sub_self]
    · obtain ⟨N, hNX, _hN, hW, hκ⟩ := hrec X hXR hbal
      have hsum : (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card • defect ((X \ N) ∪ J)) = 0 := by
        have hcoeff :
            (∑ J ∈ N.powerset,
              ∑ F ∈ R.powerset, ((-1 : ℤ) ^ J.card * κ ((X \ N) ∪ J) F) • W F) = 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro F hF
          rw [← Finset.sum_smul, hκ F (Finset.mem_powerset.mp hF), zero_smul]
        simp only [defect, smul_sub, Finset.smul_sum, smul_smul]
        rw [Finset.sum_sub_distrib, hW, hcoeff, sub_self]
      have hproper (J : Finset E) (hJ : J ∈ N.powerset) (hne : J ≠ N) :
          defect ((X \ N) ∪ J) = 0 := by
        have hJN : J ⊆ N := Finset.mem_powerset.mp hJ
        have hchild : (X \ N) ∪ J ⊆ X :=
          Finset.union_subset Finset.sdiff_subset (hJN.trans hNX)
        have hstrict : (X \ N) ∪ J ⊂ X := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hchild, ?_⟩
          intro heq
          apply hne
          apply Finset.Subset.antisymm hJN
          intro e heN
          have hechild : e ∈ (X \ N) ∪ J := by rw [heq]; exact hNX heN
          rcases Finset.mem_union.mp hechild with he | he
          · exact ((Finset.mem_sdiff.mp he).2 heN).elim
          · exact he
        exact ih _ hstrict (hchild.trans hXR)
      have hisolate :
          (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card • defect ((X \ N) ∪ J)) =
            (-1 : ℤ) ^ N.card • defect X := by
        rw [Finset.sum_eq_single N]
        · rw [Finset.sdiff_union_of_subset hNX]
        · intro J hJ hne
          rw [hproper J hJ hne, smul_zero]
        · intro hnot
          exact (hnot (Finset.mem_powerset.mpr Finset.Subset.rfl)).elim
      have hsign : (-1 : ℤ) ^ N.card * (-1 : ℤ) ^ N.card = 1 := by
        calc
          (-1 : ℤ) ^ N.card * (-1 : ℤ) ^ N.card = ((-1 : ℤ) ^ 2) ^ N.card := by
            rw [← pow_mul, two_mul, pow_add]
          _ = 1 := by simp
      rw [hisolate] at hsum
      have hcancel := congrArg (fun v : M => (-1 : ℤ) ^ N.card • v) hsum
      simpa only [smul_smul, hsign, one_smul, smul_zero] using hcancel
  intro X hXR
  exact sub_eq_zero.mp (hdefect X hXR)

end

end VerticalStripLLT.Components

import VerticalStripLLT.CyclicHessenberg.ColorMountain
import VerticalStripLLT.CyclicHessenberg.SortedSubsets
import VerticalStripLLT.Components.WordProof.DisjointSubsetSums

/-! Group homogeneous mountain words by their support.
The imported disjoint-subset lemma is purely a finite-sum bijection; it imports no word quotient
or component theorem. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V] [CommRing R]

theorem reverse_increasingSort (S : Finset V) : S.sort.reverse = S.sort (· ≥ ·) := by
  apply List.SortedGT.eq_of_mem_iff (Finset.sortedLT_sort S).reverse (Finset.sortedGT_sort S)
  intro a
  simp

theorem signedSublistMountain_eq_subsetSum (S : Finset V) (r : V) (d : ℕ) :
    signedSublistMountain (R := R) S.sort r d =
      ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
        if A.card + B.card = d then
          (-1 : R) ^ B.card • wordTerm (A.sort ++ [r] ++ B.sort (· ≥ ·)) else 0 := by
  classical
  rw [signedSublistMountain, sum_sublists_sort]
  simp_rw [sum_sublists_sort, Finset.length_sort, reverse_increasingSort]

private theorem overlapping_mountain_zero (f : List V → R)
    (hrep : ∀ l, ¬ l.Nodup → f l = 0) (A B : Finset V) (r : V)
    (hab : ¬ Disjoint A B) : ContextEq f (wordTerm (A.sort ++ [r] ++ B.sort (· ≥ ·))) 0 := by
  obtain ⟨a, ha, hb⟩ := Finset.not_disjoint_iff.mp hab
  intro ρ σ
  rw [wordEval_term, map_zero]
  apply hrep
  intro hn
  have hn' : ((ρ ++ A.sort) ++ ([r] ++ B.sort (· ≥ ·) ++ σ)).Nodup := by
    simpa only [List.append_assoc] using hn
  have hd := (List.nodup_append'.mp hn').2.2
  exact hd (show a ∈ ρ ++ A.sort by simp [ha]) (by simp [hb])

/-- The degree-`d` signed mountains, indexed by their support and their decreasing marked part. -/
noncomputable def signedSetMountain (S : Finset V) (r : V) (d : ℕ) : WordSum R V := by
  classical
  exact ∑ U ∈ S.powerset, if U.card = d then
    ∑ T ∈ U.powerset,
      (-1 : R) ^ T.card • wordTerm ((U \ T).sort ++ [r] ++ T.sort (· ≥ ·))
    else 0

/-- Overlapping choices vanish, and each surviving pair is uniquely its union and marked part. -/
theorem signedSublistMountain_eq_signedSetMountain (f : List V → R)
    (hrep : ∀ l, ¬ l.Nodup → f l = 0) (S : Finset V) (r : V) (d : ℕ) :
    ContextEq f (signedSublistMountain S.sort r d) (signedSetMountain S r d) := by
  classical
  let F : Finset V → Finset V → WordSum R V := fun A B =>
    if A.card + B.card = d then
      (-1 : R) ^ B.card • wordTerm (A.sort ++ [r] ++ B.sort (· ≥ ·)) else 0
  have hremove : ContextEq f (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, F A B)
      (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, if Disjoint A B then F A B else 0) := by
    apply ContextEq.sum
    intro A hA
    apply ContextEq.sum
    intro B hB
    by_cases hdis : Disjoint A B
    · simp only [ite_eq_left hdis]
      exact ContextEq.refl _
    · simp only [ite_eq_right hdis]
      dsimp only [F]
      split_ifs
      · simpa only [smul_zero] using (overlapping_mountain_zero f hrep A B r hdis).smul
          ((-1 : R) ^ B.card)
      · exact ContextEq.refl _
  rw [signedSublistMountain_eq_subsetSum]
  apply hremove.trans
  apply ContextEq.of_eq
  rw [VerticalStripLLT.Components.sum_powerset_disjoint_eq_union]
  unfold signedSetMountain
  apply Finset.sum_congr rfl
  intro U hU
  have hcard (T : Finset V) (hT : T ∈ U.powerset) : (U \ T).card + T.card = U.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.mem_powerset.mp hT)
  by_cases hd : U.card = d
  · simp only [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [F, hcard T hT, ite_eq_left hd]
  · simp only [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro T hT
    simp only [F, hcard T hT, ite_eq_right hd]

theorem wordAd_eq_signedSetMountain (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (S : Finset V) (r : V) (hr : ∀ a ∈ S, a < r) (d : ℕ) :
    ContextEq f (wordAd (wordLetterSum S.sort) (wordTerm [r]) d)
      (signedSetMountain S r d) := by
  have hsmall : ∀ a ∈ S.sort, a < r := fun a ha => hr a ((Finset.mem_sort _).mp ha)
  have hsort : S.sort.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
  intro ρ σ
  exact (wordAd_eq_signedSublistMountain f hf hrep S.sort r hsort hsmall d ρ σ).trans
    (signedSublistMountain_eq_signedSetMountain f hrep S r d ρ σ)

end VerticalStripLLT.CyclicHessenberg

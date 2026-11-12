import VerticalStripLLT.CyclicHessenberg.ColorSubsetMountain
import VerticalStripLLT.CyclicHessenberg.ColorElementaryExpansion
import VerticalStripLLT.CyclicHessenberg.RootDeletion

/-! The insertion coefficients are the actual signed deletion functionals. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V] [CommRing R]

/-- The mountain block on `U` with an additional largest root. -/
noncomputable def mountainWordSum (U : Finset V) (r : V) : WordSum R V :=
  ∑ T ∈ U.powerset,
    (-1 : R) ^ T.card • wordTerm ((U \ T).sort ++ [r] ++ T.sort (· ≥ ·))

theorem signedSetMountain_eq_sum (S : Finset V) (r : V) (d : ℕ) :
    signedSetMountain (R := R) S r d =
      ∑ U ∈ S.powerset, if U.card = d then mountainWordSum U r else 0 := rfl

/-- Every mountain block evaluates to the signed root-deletion kernel, with unequal suffixes. -/
theorem mountainWordSum_eval (Z : List V → List V → R) (U : Finset V) (r : V)
    (hr : r ∉ U) (π τ : List V) :
    wordEval (fun w => Z (w ++ π) (w ++ τ)) [] [] (mountainWordSum U r) =
      signedRootDeletion Z (insert r U) r π τ := by
  classical
  simp only [mountainWordSum, map_sum, map_smul, wordEval_term, List.nil_append,
    List.append_nil, smul_eq_mul, signedRootDeletion, mountainList,
    Finset.erase_insert hr]

/-- The coefficient is positive by the proved exchange theorem, not by definition. -/
theorem mountainWordSum_eval_positive {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (U : Finset V) (r : V)
    (hr : ∀ a ∈ U, a < r) (π τ : List V) :
    wordEval (fun w => Z (w ++ π) (w ++ τ)) [] [] (mountainWordSum U r) =
      rootDeletion q Z (insert r U) r π τ := by
  classical
  have hrU : r ∉ U := fun h => (lt_irrefl r) (hr r h)
  rw [mountainWordSum_eval Z U r hrU π τ]
  apply signedRootDeletion_eq_rootDeletion hZ _ _ (Finset.mem_insert_self _ _)
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact le_rfl
  · exact (hr a ha).le

/-- Collapse the homogeneous degree index, retaining each actual subset of letters. -/
theorem sum_elementary_signedSetMountain (S : Finset V) (r : V) (Y : List R) :
    (∑ d ∈ Finset.range (S.card + 1),
      elementaryWeights Y (d + 1) • signedSetMountain (R := R) S r d) =
      ∑ U ∈ S.powerset,
        elementaryWeights Y (U.card + 1) • mountainWordSum (R := R) U r := by
  classical
  simp only [signedSetMountain_eq_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have hcard : U.card < S.card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp hU))
  simp only [smul_ite, smul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_range, hcard, ite_true]

/-- The actual insertion operator has elementary-weighted signed deletion blocks. -/
theorem colorInsertion_eq_mountainSum (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (S : Finset V) (r : V) (hr : ∀ a ∈ S, a < r)
    (hdegree : ∀ w : List V, S.card + 1 < w.length → f w = 0) (Y : List R) :
    ContextEq f (colorInsertion S.sort r Y)
      (∑ U ∈ S.powerset, elementaryWeights Y (U.card + 1) • mountainWordSum U r) := by
  classical
  have hsmall : ∀ a ∈ S.sort, a < r := by
    intro a ha
    exact hr a (by simpa only [Finset.mem_sort] using ha)
  have hsort : S.sort.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
  have hall (d : ℕ) : ContextEq f
      (wordAd (wordLetterSum S.sort) (wordTerm [r]) d) (signedSetMountain S r d) :=
    wordAd_eq_signedSetMountain f hf hrep S r hr d
  generalize hl : S.sort = l at hsmall hsort hall ⊢
  have h₁ := colorInsertion_eq_adExpansion f hf hrep (S.card + 1) hdegree
    l r hsort hsmall Y
  have h₂ := ContextEq.sum (f := f) (Finset.range (S.card + 1))
    (fun d => elementaryWeights Y (d + 1) • wordAd (wordLetterSum l) (wordTerm [r]) d)
    (fun d => elementaryWeights Y (d + 1) • signedSetMountain S r d)
    (fun d _ => (hall d).smul (elementaryWeights Y (d + 1)))
  exact h₁.trans (h₂.trans (ContextEq.of_eq (sum_elementary_signedSetMountain S r Y)))

end VerticalStripLLT.CyclicHessenberg

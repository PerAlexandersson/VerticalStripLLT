import VerticalStripLLT.CyclicHessenberg.ColorDegree
import VerticalStripLLT.CyclicHessenberg.ColorClassProducts
import Mathlib.Algebra.BigOperators.Ring.List

/-! Isolating homogeneous signed mountain words by finite length slices. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [CommRing R]

def lengthSlice (f : List V → R) (M : ℕ) (w : List V) : R :=
  if w.length = M then f w else 0

theorem lengthSlice_repeated (f : List V → R)
    (hf : ∀ w, ¬ w.Nodup → f w = 0) (M : ℕ) :
    ∀ w, ¬ w.Nodup → lengthSlice f M w = 0 := by
  intro w hw
  simp only [lengthSlice, hf w hw, ite_self]

theorem lengthSlice_degree (f : List V → R) (M : ℕ) :
    ∀ w, M < w.length → lengthSlice f M w = 0 := by
  intro w hw
  exact ite_eq_right (ne_of_gt hw)

theorem ContextualBalance.lengthSlice [LinearOrder V] {f : List V → R}
    (hf : ContextualBalance f) (M : ℕ) : ContextualBalance (lengthSlice f M) := by
  intro ρ σ a b c hab hbc
  have hh := hf ρ σ a b c hab hbc
  simp only [CyclicHessenberg.lengthSlice, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp_all

theorem wordEval_sub_function (f g : List V → R) (ρ σ : List V) (A : WordSum R V) :
    wordEval (fun w => f w - g w) ρ σ A = wordEval f ρ σ A - wordEval g ρ σ A := by
  induction A using MonoidAlgebra.induction_on with
  | of w =>
    change wordEval _ _ _ (wordTerm w.toList) =
      wordEval _ _ _ (wordTerm w.toList) - wordEval _ _ _ (wordTerm w.toList)
    simp only [wordEval_term]
  | add A B hA hB => simp only [map_add, hA, hB]; abel
  | smul c A hA => simp only [map_smul, hA, smul_sub]

theorem wordAd_eval_congr_of_length (f g : List V → R) (l : List V) (r : V)
    (d : ℕ) (ρ σ : List V)
    (hfg : ∀ w, w.length = ρ.length + d + 1 + σ.length → f w = g w) :
    wordEval f ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) =
      wordEval g ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) := by
  have hh := wordAd_eval_zero_of_length (fun w => f w - g w) l r d ρ σ
    (fun w hw => sub_eq_zero.mpr (hfg w hw))
  rw [wordEval_sub_function, sub_eq_zero] at hh
  exact hh

/-- A length slice keeps exactly the homogeneous component indicated by the exterior lengths. -/
theorem wordAd_eval_lengthSlice (f : List V → R) (M : ℕ) (l : List V) (r : V)
    (d : ℕ) (ρ σ : List V) :
    wordEval (lengthSlice f M) ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) =
      if ρ.length + d + 1 + σ.length = M then
        wordEval f ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) else 0 := by
  by_cases hm : ρ.length + d + 1 + σ.length = M
  · rw [ite_eq_left hm]
    apply wordAd_eval_congr_of_length
    intro w hw
    simp only [lengthSlice, hw, hm, ite_eq_left]
  · rw [ite_eq_right hm]
    apply wordAd_eval_zero_of_length
    intro w hw
    simp only [lengthSlice, hw, ite_eq_right hm]

/-- Inverse conjugation is a finite telescope with an explicitly vanishing last term. -/
theorem inverseClass_root_eq_adSum [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (N : ℕ) (hdegree : ∀ w : List V, N < w.length → f w = 0)
    (l : List V) (r : V) (hl : l.Pairwise (· < ·))
    (hr : ∀ a ∈ l, a < r) :
    ContextEq f (inverseClass (-1) l * wordTerm [r] * descendingClass (-1) l)
      (∑ d ∈ Finset.range N, wordAd (wordLetterSum l) (wordTerm [r]) d) := by
  classical
  let U : ℕ → WordSum R V := wordAd (wordLetterSum l) (wordTerm [r])
  let D : WordSum R V := descendingClass (-1) l
  let I : WordSum R V := inverseClass (-1) l
  let T : WordSum R V := ∑ d ∈ Finset.range N, U d
  have hsum := ContextEq.sum (f := f) (Finset.range N)
    (fun d => D * U d * I) (fun d => U d - U (d + 1)) (fun d _ => by
      simpa only [neg_one_smul, sub_eq_add_neg] using
        descendingClass_conjugate_ad f hf hrep (-1) l r hl hr d)
  have hsum' : ContextEq f (D * T * I) (U 0 - U N) := by
    simpa only [T, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_sub'] using hsum
  have hlast : ContextEq f (U N) 0 := wordAd_terminates f N hdegree l r N le_rfl
  have hroot : ContextEq f (D * T * I) (wordTerm [r]) :=
    hsum'.trans (by simpa only [sub_zero, U, wordAd] using (ContextEq.refl (U 0)).sub hlast)
  have hmain := (hroot.mul_left I).mul_right D
  have hID := inverseClass_mul_descendingClass f hrep (-1) l
  have hcollapse : ContextEq f (I * (D * T * I) * D) T := by
    have hh := (hID.mul_right T).mul hID
    simpa only [one_mul, mul_one, mul_assoc] using hh
  exact hmain.symm.trans hcollapse

/-- Homogeneous projection isolates one commutator without polynomial coefficient assumptions. -/
theorem wordAd_eq_lengthSlice_inverseRoot [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (l : List V) (r : V) (hl : l.Pairwise (· < ·))
    (hr : ∀ a ∈ l, a < r) (d : ℕ) (ρ σ : List V) :
    wordEval f ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) =
      wordEval (lengthSlice f (ρ.length + d + 1 + σ.length)) ρ σ
        (inverseClass (-1) l * wordTerm [r] * descendingClass (-1) l) := by
  classical
  let M := ρ.length + d + 1 + σ.length
  have hh := inverseClass_root_eq_adSum (lengthSlice f M) (hf.lengthSlice M)
    (lengthSlice_repeated f hrep M) M (lengthSlice_degree f M) l r hl hr ρ σ
  rw [map_sum] at hh
  simp_rw [wordAd_eval_lengthSlice] at hh
  have heq (j : ℕ) : ρ.length + j + 1 + σ.length = M ↔ j = d := by
    dsimp [M]
    lia
  simp_rw [heq] at hh
  have hd : d ∈ Finset.range M := by simp only [Finset.mem_range]; dsimp [M]; lia
  simpa only [Finset.sum_ite_eq', ite_eq_left hd] using hh.symm

/-- Literal expansion of inverse conjugation, before discarding repeated vertices. -/
theorem inverseRoot_eq_sublistSum (l : List V) (r : V) :
    inverseClass (-1 : R) l * wordTerm [r] * descendingClass (-1) l =
      (l.sublists.map fun A => (l.sublists.map fun B =>
        (-1 : R) ^ B.length • wordTerm (A ++ [r] ++ B.reverse)).sum).sum := by
  rw [inverseClass_eq_sublistSum, descendingClass_eq_sublistSum]
  simp only [neg_neg, one_pow, one_smul]
  simp_rw [← List.sum_map_mul_right]
  simp_rw [← List.sum_map_mul_left, mul_smul_comm, wordTerm_mul]

/-- All signed sublist mountains of one homogeneous degree. Repetitions are still present. -/
noncomputable def signedSublistMountain (l : List V) (r : V) (d : ℕ) : WordSum R V :=
  (l.sublists.map fun A => (l.sublists.map fun B =>
    if A.length + B.length = d then
      (-1 : R) ^ B.length • wordTerm (A ++ [r] ++ B.reverse) else 0).sum).sum

theorem lengthSlice_inverseRoot_eval (f : List V → R) (l : List V) (r : V)
    (d : ℕ) (ρ σ : List V) :
    wordEval (lengthSlice f (ρ.length + d + 1 + σ.length)) ρ σ
        (inverseClass (-1) l * wordTerm [r] * descendingClass (-1) l) =
      wordEval f ρ σ (signedSublistMountain l r d) := by
  classical
  rw [inverseRoot_eq_sublistSum, signedSublistMountain]
  simp only [map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro A hA
  simp only [map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro B hB
  have hlen : (ρ ++ (A ++ [r] ++ B.reverse) ++ σ).length =
      ρ.length + d + 1 + σ.length ↔ A.length + B.length = d := by
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
    lia
  by_cases hd : A.length + B.length = d
  · simp only [ite_eq_left hd, map_smul, wordEval_term, lengthSlice,
      ite_eq_left (hlen.mpr hd)]
  · simp only [ite_eq_right hd, map_zero, map_smul, wordEval_term, lengthSlice,
      ite_eq_right (fun h => hd (hlen.mp h)), smul_zero]

/-- The iterated commutator is the signed mountain sum in every exterior context. -/
theorem wordAd_eq_signedSublistMountain [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (l : List V) (r : V) (hl : l.Pairwise (· < ·))
    (hr : ∀ a ∈ l, a < r) (d : ℕ) :
    ContextEq f (wordAd (wordLetterSum l) (wordTerm [r]) d)
      (signedSublistMountain l r d) := by
  intro ρ σ
  exact (wordAd_eq_lengthSlice_inverseRoot f hf hrep l r hl hr d ρ σ).trans
    (lengthSlice_inverseRoot_eval f l r d ρ σ)

end VerticalStripLLT.CyclicHessenberg

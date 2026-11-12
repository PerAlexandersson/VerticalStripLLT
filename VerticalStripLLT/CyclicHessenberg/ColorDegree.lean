import VerticalStripLLT.CyclicHessenberg.ColorConjugation
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Explicit finite-degree termination for the color-insertion commutators. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [CommRing R]

theorem wordEval_letterSum_mul (f : List V → R) (ρ σ l : List V) (Y : WordSum R V) :
    wordEval f ρ σ (wordLetterSum l * Y) =
      (l.map fun a => wordEval f (ρ ++ [a]) σ Y).sum := by
  induction l with
  | nil => simp [wordLetterSum]
  | cons a l ih => simp [wordLetterSum, add_mul, wordEval_term_mul, ih]

theorem wordEval_mul_letterSum (f : List V → R) (ρ σ l : List V) (Y : WordSum R V) :
    wordEval f ρ σ (Y * wordLetterSum l) =
      (l.map fun a => wordEval f ρ ([a] ++ σ) Y).sum := by
  induction l with
  | nil => simp [wordLetterSum]
  | cons a l ih => simp [wordLetterSum, mul_add, wordEval_mul_term, ih]

/-- Every term in the `d`th commutator has exactly `d+1` letters. -/
theorem wordAd_eval_zero_of_length (f : List V → R) (l : List V) (r : V)
    (d : ℕ) (ρ σ : List V)
    (hf : ∀ w : List V, w.length = ρ.length + d + 1 + σ.length → f w = 0) :
    wordEval f ρ σ (wordAd (wordLetterSum l) (wordTerm [r]) d) = 0 := by
  induction d generalizing ρ σ with
  | zero =>
    rw [wordAd, wordEval_term]
    apply hf
    simp only [List.length_append, List.length_cons, List.length_nil]
    lia
  | succ d ih =>
    rw [wordAd, wordComm, map_sub, wordEval_letterSum_mul, wordEval_mul_letterSum]
    have hleft : (l.map fun a =>
        wordEval f (ρ ++ [a]) σ (wordAd (wordLetterSum l) (wordTerm [r]) d)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      apply ih
      intro w hw
      apply hf
      simp only [List.length_append, List.length_singleton] at hw
      lia
    have hright : (l.map fun a =>
        wordEval f ρ ([a] ++ σ) (wordAd (wordLetterSum l) (wordTerm [r]) d)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      apply ih
      intro w hw
      apply hf
      simp only [List.length_append, List.length_singleton] at hw
      lia
    rw [hleft, hright, sub_self]

/-- An explicit truncation bound valid in every exterior context. -/
theorem wordAd_terminates (f : List V → R) (N : ℕ)
    (hf : ∀ w : List V, N < w.length → f w = 0)
    (l : List V) (r : V) (d : ℕ) (hd : N ≤ d) :
    ContextEq f (wordAd (wordLetterSum l) (wordTerm [r]) d) 0 := by
  intro ρ σ
  rw [map_zero]
  apply wordAd_eval_zero_of_length
  intro w hw
  exact hf w (by lia)

/-- Zero extension of an actual support functional has precisely the needed finite bound. -/
theorem kernelEntry_diagonal_degree_bound [LinearOrder V] (S : Finset V)
    (Z : Kernel R S) (w : List V) (hw : S.card < w.length) : kernelEntry Z w w = 0 := by
  classical
  have hnot : ¬ IsOrder S w := fun h => by have hh := h.length; lia
  simp only [kernelEntry, dite_eq_right hnot]

theorem kernelEntry_diagonal_repeated [LinearOrder V] (S : Finset V)
    (Z : Kernel R S) (w : List V) (hw : ¬ w.Nodup) : kernelEntry Z w w = 0 := by
  classical
  have hnot : ¬ IsOrder S w := fun h => hw h.1
  simp only [kernelEntry, dite_eq_right hnot]

end VerticalStripLLT.CyclicHessenberg

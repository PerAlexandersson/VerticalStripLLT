import VerticalStripLLT.CyclicHessenberg.ColorInsertion
import VerticalStripLLT.CyclicHessenberg.ColorElementaryWeights

/-! The finite elementary-weight expansion of the independently defined insertion operator. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [CommRing R]

noncomputable def colorAdExpansion (N : ℕ) (l : List V) (r : V) (Y : List R) :
    WordSum R V :=
  ∑ d ∈ Finset.range N,
    elementaryWeights Y (d + 1) • wordAd (wordLetterSum l) (wordTerm [r]) d

/-- Adding colors gives elementary weights; the endpoint vanishes by the actual degree bound. -/
theorem colorInsertion_eq_adExpansion [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (N : ℕ) (hdegree : ∀ w : List V, N < w.length → f w = 0)
    (l : List V) (r : V) (hl : l.Pairwise (· < ·))
    (hr : ∀ a ∈ l, a < r) (Y : List R) :
    ContextEq f (colorInsertion l r Y) (colorAdExpansion N l r Y) := by
  classical
  induction Y with
  | nil =>
    simp only [colorInsertion, colorAdExpansion, elementaryWeights_nil_succ,
      zero_smul, Finset.sum_const_zero]
    exact ContextEq.refl _
  | cons t Y ih =>
    let U : ℕ → WordSum R V := wordAd (wordLetterSum l) (wordTerm [r])
    let E : ℕ → R := elementaryWeights Y
    let D : WordSum R V := descendingClass t l
    let I : WordSum R V := inverseClass t l
    have h₁ := (ContextEq.refl (t • wordTerm [r])).add ((ih.mul_left D).mul_right I)
    have hsum := ContextEq.sum (f := f) (Finset.range N)
      (fun d => E (d + 1) • (D * U d * I))
      (fun d => E (d + 1) • (U d + t • U (d + 1)))
      (fun d _ => (descendingClass_conjugate_ad f hf hrep t l r hl hr d).smul (E (d + 1)))
    have h₂ : ContextEq f (D * colorAdExpansion N l r Y * I)
        (∑ d ∈ Finset.range N, E (d + 1) • (U d + t • U (d + 1))) := by
      simpa only [colorAdExpansion, Finset.mul_sum, Finset.sum_mul,
        mul_smul_comm, smul_mul_assoc, E, U] using hsum
    have hterm : ContextEq f ((t * E N) • U N) 0 := by
      simpa only [smul_zero] using
        (wordAd_terminates f N hdegree l r N le_rfl).smul (t * E N)
    have hshift : colorAdExpansion N l r (t :: Y) =
        (t • wordTerm [r] +
          ∑ d ∈ Finset.range N, E (d + 1) • (U d + t • U (d + 1))) -
            (t * E N) • U N := by
      simpa only [colorAdExpansion, elementaryWeights_cons_succ, U, E, wordAd] using
        finite_weight_shift E (elementaryWeights_zero Y) U t N
    have h₃ : ContextEq f (colorAdExpansion N l r (t :: Y))
        (t • wordTerm [r] +
          ∑ d ∈ Finset.range N, E (d + 1) • (U d + t • U (d + 1))) := by
      exact (ContextEq.of_eq hshift).trans (by
        simpa only [sub_zero] using (ContextEq.refl _).sub hterm)
    exact h₁.trans (((ContextEq.refl _).add h₂).trans h₃.symm)

end VerticalStripLLT.CyclicHessenberg

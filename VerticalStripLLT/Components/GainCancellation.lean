import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-! Sign-reversing cancellation on a finite powerset. -/

namespace VerticalStripLLT.Components

open scoped BigOperators
open Classical

noncomputable section

variable {E : Type*} [DecidableEq E]

/-- Toggle the edge selected by e, inserting it when absent and erasing it
when present. -/
def toggleSubset (e : Finset E → E) (J : Finset E) : Finset E :=
  if e J ∈ J then J.erase (e J) else insert (e J) J

/-- A potential-dependent toggle cancels the signed sum over all good subsets.
The edge selector may depend on the current subset, provided it is unchanged
by its own toggle. -/
theorem sum_powerset_good_toggle_eq_zero
    (N : Finset E) (Good : Finset E → Prop) (e : Finset E → E)
    (hmem : ∀ J ∈ N.powerset, Good J → e J ∈ N)
    (hgood : ∀ J ∈ N.powerset, Good J →
      Good (toggleSubset e J))
    (heq : ∀ J ∈ N.powerset, Good J →
      e (toggleSubset e J) = e J) :
    (∑ J ∈ N.powerset, if Good J then (-1 : ℤ) ^ J.card else 0) = 0 := by
  classical
  let f : Finset E → ℤ :=
    fun J => if Good J then (-1 : ℤ) ^ J.card else 0
  let g : ∀ J ∈ N.powerset, Finset E :=
    fun J _ => if Good J then toggleSubset e J else J
  have g_mem : ∀ J (hJ : J ∈ N.powerset), g J hJ ∈ N.powerset := by
    intro J hJ
    have hsub : J ⊆ N := Finset.mem_powerset.mp hJ
    by_cases hJGood : Good J
    · simp only [g, ite_eq_left hJGood]
      unfold toggleSubset
      split_ifs with heJ
      · exact Finset.mem_powerset.mpr
          ((Finset.erase_subset _ _).trans hsub)
      · exact Finset.mem_powerset.mpr
          (Finset.insert_subset (hmem J hJ hJGood) hsub)
    · simp only [g, ite_eq_right hJGood]
      exact hJ
  have g_involutive :
      ∀ J (hJ : J ∈ N.powerset), g (g J hJ) (g_mem J hJ) = J := by
    intro J hJ
    by_cases hJGood : Good J
    · have hTgood : Good (toggleSubset e J) := hgood J hJ hJGood
      have heqJ : e (toggleSubset e J) = e J := heq J hJ hJGood
      simp only [g, ite_eq_left hJGood, ite_eq_left hTgood]
      rw [toggleSubset, heqJ]
      by_cases heJ : e J ∈ J <;> simp [toggleSubset, heJ]
    · simp only [g, ite_eq_right hJGood]
  have g_sum_zero :
      ∀ J (hJ : J ∈ N.powerset),
        f J + f (g J hJ) = 0 := by
    intro J hJ
    by_cases hJGood : Good J
    · have hTgood : Good (toggleSubset e J) := hgood J hJ hJGood
      simp only [f, g, ite_eq_left hJGood, ite_eq_left hTgood]
      unfold toggleSubset
      split_ifs with hJmem
      · have hcard : J.card = (J.erase (e J)).card + 1 :=
          (Finset.card_erase_add_one hJmem).symm
        rw [hcard, pow_succ]
        ring
      · rw [Finset.card_insert_of_notMem hJmem]
        rw [pow_succ]
        ring
    · simp only [f, g, ite_eq_right hJGood, add_zero]
  have g_ne :
      ∀ J (hJ : J ∈ N.powerset), f J ≠ 0 → g J hJ ≠ J := by
    intro J hJ hJf
    have hJGood : Good J := by
      by_contra hnot
      exact hJf (by simp [f, hnot])
    simp only [g, ite_eq_left hJGood]
    unfold toggleSubset
    split_ifs with hJmem
    · exact Finset.erase_ne_self.mpr hJmem
    · exact Finset.insert_ne_self.mpr hJmem
  have hsum := Finset.sum_involution (s := N.powerset) (f := f) g
    g_sum_zero g_ne g_mem g_involutive
  simpa [f] using hsum

end

end VerticalStripLLT.Components

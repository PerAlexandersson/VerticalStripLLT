import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! A nontrivial finite equal-sum occupancy difference has both signs. -/

namespace VerticalStripLLT.Circular.DiagramProof

theorem exists_surplus_and_deficit_of_sum_eq
    {I : Type*} [Fintype I] (a b : I → ℕ)
    (hsum : (∑ i, a i) = ∑ i, b i) (hne : a ≠ b) :
    ∃ e f, b e < a e ∧ a f < b f := by
  have hdiff : ∃ i, a i ≠ b i := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hsurplus : ∃ e, b e < a e := by
    by_contra hno
    have hle : ∀ i ∈ (Finset.univ : Finset I), a i ≤ b i := by
      intro i hi
      exact Nat.le_of_not_gt (fun hlt => hno ⟨i, hlt⟩)
    obtain ⟨i, hi⟩ := hdiff
    have hlt : a i < b i := by
      exact lt_of_le_of_ne (hle i (Finset.mem_univ _)) hi
    have hsumlt : (∑ i, a i) < ∑ i, b i := by
      exact Finset.sum_lt_sum hle ⟨i, Finset.mem_univ _, hlt⟩
    lia
  obtain ⟨e, he⟩ := hsurplus
  have hdeficit : ∃ f, a f < b f := by
    by_contra hno
    have hle : ∀ i ∈ (Finset.univ : Finset I), b i ≤ a i := by
      intro i hi
      exact Nat.le_of_not_gt (fun hlt => hno ⟨i, hlt⟩)
    have hlt : b e < a e := he
    have hsumlt : (∑ i, b i) < ∑ i, a i := by
      exact Finset.sum_lt_sum hle ⟨e, Finset.mem_univ _, hlt⟩
    lia
  obtain ⟨f, hf⟩ := hdeficit
  exact ⟨e, f, he, hf⟩

end VerticalStripLLT.Circular.DiagramProof

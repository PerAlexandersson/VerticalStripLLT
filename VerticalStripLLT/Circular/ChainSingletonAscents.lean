import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! Counting ascents between a strictly increasing chain and one singleton. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

theorem indicator_chain_singleton_split {m : ℕ} {a b z : Fin m}
    (hab : a < b) (P : Prop) [Decidable P] :
    (if P ∧ a < z then 1 else 0) + (if P ∧ z < b then 1 else 0) =
      (if P then 1 else 0) + (if P ∧ a < z ∧ z < b then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, true_and, ite_true]
    by_cases haz : a < z <;> by_cases hzb : z < b
    all_goals simp [haz, hzb]
    all_goals lia
  · simp [hP]

theorem chain_singleton_ascents {k m : ℕ} (c : Fin (k + 1) → Fin m)
    (hc : StrictMono c) (z : Fin m)
    (A B : Fin (k + 1) → Prop) [DecidablePred A] [DecidablePred B]
    (hmatch : ∀ i : Fin k, B i.succ ↔ A i.castSucc) :
    (∑ i : Fin (k + 1),
      ((if A i ∧ c i < z then 1 else 0) +
        (if B i ∧ z < c i then 1 else 0))) =
      (∑ i : Fin k, if A i.castSucc then 1 else 0) +
        (if B 0 ∧ z < c 0 then 1 else 0) +
        (if A (Fin.last k) ∧ c (Fin.last k) < z then 1 else 0) +
        (∑ i : Fin k,
          if A i.castSucc ∧ c i.castSucc < z ∧ z < c i.succ then 1 else 0) := by
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_castSucc (fun i => if A i ∧ c i < z then 1 else 0),
    Fin.sum_univ_succ (fun i => if B i ∧ z < c i then 1 else 0)]
  have hsplit : ∀ i : Fin k,
      (if A i.castSucc ∧ c i.castSucc < z then 1 else 0) +
          (if B i.succ ∧ z < c i.succ then 1 else 0) =
        (if A i.castSucc then 1 else 0) +
          (if A i.castSucc ∧ c i.castSucc < z ∧ z < c i.succ then 1 else 0) := by
    intro i
    simpa only [hmatch i] using
      indicator_chain_singleton_split (hc (Fin.castSucc_lt_succ (i := i))) (A i.castSucc)
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hsplit i)
  simp only [Finset.sum_add_distrib] at hs
  lia

end VerticalStripLLT.Circular

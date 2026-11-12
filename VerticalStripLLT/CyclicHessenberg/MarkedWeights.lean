import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Coeff

/-! Binomial weights count subsets of marked events by their cardinality. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- Expand the binomial weight as a sum indexed by subsets of the event set. -/
theorem x_pow_mul_one_add_X_pow_eq_sum_powerset {α : Type*} [DecidableEq α]
    (E : Finset α) (d : ℕ) :
    (Polynomial.X : Polynomial ℕ) ^ d * (1 + (Polynomial.X : Polynomial ℕ)) ^ E.card =
      ∑ T ∈ E.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + T.card) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ,
      Finset.sum_powerset_insert ha]
    have hsecond :
        (∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + (insert a T).card)) =
          (Polynomial.X : Polynomial ℕ) *
            ∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + T.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      have hnot : a ∉ T := Finset.notMem_mono (Finset.mem_powerset.mp hT) ha
      rw [Finset.card_insert_of_notMem hnot, ← Nat.add_assoc, pow_succ, mul_comm]
    calc
      (Polynomial.X : Polynomial ℕ) ^ d *
          ((1 + (Polynomial.X : Polynomial ℕ)) ^ s.card *
            (1 + (Polynomial.X : Polynomial ℕ))) =
          (Polynomial.X : Polynomial ℕ) ^ d * (1 + (Polynomial.X : Polynomial ℕ)) ^ s.card +
            (Polynomial.X : Polynomial ℕ) *
              ((Polynomial.X : Polynomial ℕ) ^ d *
                (1 + (Polynomial.X : Polynomial ℕ)) ^ s.card) := by
        simp only [mul_add, mul_one]
        congr 1
        rw [← mul_assoc, mul_comm]
      _ = (∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + T.card)) +
            (Polynomial.X : Polynomial ℕ) *
            ∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + T.card) := by
        rw [ih]
      _ = (∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + T.card)) +
            ∑ T ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ (d + (insert a T).card) := by
        rw [hsecond]

/-- The coefficient at degree `j` counts subsets of marked events of the
required size. -/
theorem coeff_X_pow_mul_one_add_X_pow_card {α : Type*} [DecidableEq α]
    (E : Finset α) (d j : ℕ) :
    ((Polynomial.X : Polynomial ℕ) ^ d * (1 + (Polynomial.X : Polynomial ℕ)) ^ E.card).coeff j =
      (E.powerset.filter (fun T => j = d + T.card)).card := by
  rw [x_pow_mul_one_add_X_pow_eq_sum_powerset]
  simp [Polynomial.coeff_X_pow]

end VerticalStripLLT.CyclicHessenberg

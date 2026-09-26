import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Finite algebra for expanding ascent factors into selected edge subsets. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

/-- The completed Aristotle candidate from task `a9e608b9-2049-4c1c-a62e-26a550d317c8`,
ported with minimal imports. -/
theorem pow_filter_card_eq_sum_powerset {E R : Type*} [DecidableEq E] [CommSemiring R]
    (t : Finset E) (p : E → Prop) [DecidablePred p] (z : R) :
    (z + 1) ^ (t.filter p).card =
      ∑ A ∈ t.powerset, if (∀ e ∈ A, p e) then z ^ A.card else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_pow_mul_eq_add_pow]
  simp only [one_pow, mul_one]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext A
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
  constructor
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
  · intro h x hx
    exact ⟨h.1 hx, h.2 x hx⟩

/-- Expand the ascent factors of a finite coloring sum into selected edge subsets.
This is purely algebraic and assumes neither an HRV formula nor acyclicity. -/
theorem finite_subset_coloring_expansion
    {I E R : Type*} [Fintype I] [DecidableEq E] [CommSemiring R]
    (t : Finset E) (ok : I → Prop) (asc : I → E → Prop)
    [DecidablePred ok] [∀ i, DecidablePred (asc i)] (w : I → R) (z : R) :
    (∑ i, if ok i then (z + 1) ^ (t.filter (asc i)).card * w i else 0) =
      ∑ A ∈ t.powerset, z ^ A.card *
        ∑ i, if ok i ∧ (∀ e ∈ A, asc i e) then w i else 0 := by
  simp_rw [pow_filter_card_eq_sum_powerset, Finset.sum_mul, Finset.mul_sum]
  have hsum : ∀ i, (if ok i then ∑ A ∈ t.powerset,
      (if (∀ e ∈ A, asc i e) then z ^ A.card else 0) * w i else 0) =
      ∑ A ∈ t.powerset, z ^ A.card * (if ok i ∧ (∀ e ∈ A, asc i e) then w i else 0) := by
    intro i
    split_ifs with h
    · apply Finset.sum_congr rfl
      intro A _
      by_cases hA : ∀ e ∈ A, asc i e <;> simp [h, hA]
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_comm]

end VerticalStripLLT.Circular

import VerticalStripLLT.Coloring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Split finite colorings of a concatenation and factor independent coloring sums. -/

namespace VerticalStripLLT

open scoped BigOperators

def coloringSplitEquiv (n k m : ℕ) :
    (Fin (n + k) → Fin m) ≃ ((Fin n → Fin m) × (Fin k → Fin m)) where
  toFun c := (c ∘ Fin.castAdd k, c ∘ Fin.natAdd n)
  invFun p := Fin.addCases p.1 p.2
  left_inv c := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp

@[simp] theorem coloringSplitEquiv_left (n k m : ℕ)
    (c : Fin (n + k) → Fin m) (i : Fin n) :
    (coloringSplitEquiv n k m c).1 i = c (Fin.castAdd k i) := rfl

@[simp] theorem coloringSplitEquiv_right (n k m : ℕ)
    (c : Fin (n + k) → Fin m) (j : Fin k) :
    (coloringSplitEquiv n k m c).2 j = c (Fin.natAdd n j) := rfl

@[simp] theorem coloringSplitEquiv_apply_left (n k m : ℕ)
    (a : Fin n → Fin m) (b : Fin k → Fin m) (i : Fin n) :
    (coloringSplitEquiv n k m).symm (a, b) (Fin.castAdd k i) = a i := by
  simp [coloringSplitEquiv]

@[simp] theorem coloringSplitEquiv_apply_right (n k m : ℕ)
    (a : Fin n → Fin m) (b : Fin k → Fin m) (j : Fin k) :
    (coloringSplitEquiv n k m).symm (a, b) (Fin.natAdd n j) = b j := by
  simp [coloringSplitEquiv]

theorem sum_colorings_split {n k m : ℕ}
    (f : (Fin n → Fin m) → (Fin k → Fin m) → XPoly m) :
    ∑ c : Fin (n + k) → Fin m,
        f (coloringSplitEquiv n k m c).1 (coloringSplitEquiv n k m c).2 =
      ∑ a : Fin n → Fin m, ∑ b : Fin k → Fin m, f a b := by
  classical
  rw [show (∑ c : Fin (n + k) → Fin m,
      f (coloringSplitEquiv n k m c).1 (coloringSplitEquiv n k m c).2) =
      ∑ p : (Fin n → Fin m) × (Fin k → Fin m), f p.1 p.2 by
        exact Fintype.sum_equiv (coloringSplitEquiv n k m) _ _ (by
          intro p
          simp)]
  rw [Fintype.sum_prod_type]

theorem sum_colorings_split_mul {n k m : ℕ}
    (f : (Fin n → Fin m) → XPoly m) (g : (Fin k → Fin m) → XPoly m) :
    ∑ c : Fin (n + k) → Fin m,
        f (coloringSplitEquiv n k m c).1 * g (coloringSplitEquiv n k m c).2 =
      (∑ a : Fin n → Fin m, f a) * ∑ b : Fin k → Fin m, g b := by
  rw [show (∑ c : Fin (n + k) → Fin m,
      f (coloringSplitEquiv n k m c).1 * g (coloringSplitEquiv n k m c).2) =
      ∑ a : Fin n → Fin m, ∑ b : Fin k → Fin m, f a * g b by
        exact sum_colorings_split (fun a b => f a * g b)]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

end VerticalStripLLT

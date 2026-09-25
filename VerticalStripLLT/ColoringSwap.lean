import VerticalStripLLT.Coloring
import Mathlib.Algebra.BigOperators.Fin

/-! Color swaps and monomial preservation, independently of bounce graph hypotheses. -/

namespace VerticalStripLLT

open scoped BigOperators

def swapColors {n m : ℕ} (a b : Fin n) (c : Fin n → Fin m) : Fin n → Fin m :=
  c ∘ Equiv.swap a b

@[simp] theorem swapColors_apply_left {n m : ℕ} (a b : Fin n) (c : Fin n → Fin m) :
    swapColors a b c a = c b := by
  simp [swapColors]

@[simp] theorem swapColors_apply_right {n m : ℕ} (a b : Fin n) (c : Fin n → Fin m) :
    swapColors a b c b = c a := by
  simp [swapColors]

theorem swapColors_apply_of_ne_of_ne {n m : ℕ} (a b j : Fin n) (c : Fin n → Fin m)
    (hja : j ≠ a) (hjb : j ≠ b) : swapColors a b c j = c j := by
  simp [swapColors, Equiv.swap_apply_of_ne_of_ne hja hjb]

@[simp] theorem swapColors_involutive {n m : ℕ} (a b : Fin n) (c : Fin n → Fin m) :
    swapColors a b (swapColors a b c) = c := by
  funext j
  simp [swapColors]

theorem prod_X_swapColors {n m : ℕ} (a b : Fin n) (c : Fin n → Fin m) :
    (∏ i, (MvPolynomial.X (swapColors a b c i) : XPoly m)) =
      ∏ i, MvPolynomial.X (c i) := by
  simpa [swapColors, Function.comp_def] using
    (Equiv.prod_comp (Equiv.swap a b) (fun i : Fin n => (MvPolynomial.X (c i) : XPoly m)))

def swapColorEquiv {n m : ℕ} (a b : Fin n) :
    {c : Fin n → Fin m // c a < c b} ≃ {c : Fin n → Fin m // c b < c a} where
  toFun c := ⟨swapColors a b c.1, by simpa using c.2⟩
  invFun c := ⟨swapColors a b c.1, by simpa using c.2⟩
  left_inv c := by
    ext j
    simp [swapColors]
  right_inv c := by
    ext j
    simp [swapColors]

end VerticalStripLLT

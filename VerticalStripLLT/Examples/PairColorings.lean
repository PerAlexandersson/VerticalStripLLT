import VerticalStripLLT.ElementaryColorings
import Mathlib.Tactic.FinCases

/-! Alphabet-uniform two-vertex coloring sums used by the circular first slice. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

theorem sum_pair_colorings {m : ℕ} (f : Fin m → Fin m → XPoly m) :
    (∑ c : Fin 2 → Fin m, f (c 0) (c 1)) = ∑ a, ∑ b, f a b := by
  calc
    _ = ∑ p : Fin m × Fin m, f p.1 p.2 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin m)) (fun c => f (c 0) (c 1))
        (fun p => f p.1 p.2) (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem strictMono_pair_iff {m : ℕ} (c : Fin 2 → Fin m) :
    StrictMono c ↔ c 0 < c 1 := by
  constructor
  · intro h
    exact h (by decide : (0 : Fin 2) < 1)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem sum_pair_strict (m : ℕ) :
    (∑ c : Fin 2 → Fin m,
      if c 0 < c 1 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0) =
      MvPolynomial.esymm (Fin m) Q 2 := by
  simpa only [increasingColoringSum, strictMono_pair_iff, Fin.prod_univ_two] using
    increasingColoringSum_eq_esymm 2 m

theorem sum_pair_reverse_strict (m : ℕ) :
    (∑ c : Fin 2 → Fin m,
      if c 1 < c 0 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0) =
      MvPolynomial.esymm (Fin m) Q 2 := by
  rw [sum_pair_colorings (fun a b =>
    if b < a then MvPolynomial.X a * MvPolynomial.X b else 0)]
  rw [Finset.sum_comm]
  have h := sum_pair_strict m
  rw [sum_pair_colorings (fun a b =>
    if a < b then MvPolynomial.X a * MvPolynomial.X b else 0)] at h
  simpa only [mul_comm] using h

theorem sum_pair_unrestricted (m : ℕ) :
    (∑ c : Fin 2 → Fin m, MvPolynomial.X (c 0) * MvPolynomial.X (c 1)) =
      (MvPolynomial.esymm (Fin m) Q 1) ^ 2 := by
  rw [sum_pair_colorings (fun a b => MvPolynomial.X a * MvPolynomial.X b),
    MvPolynomial.esymm_one, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end VerticalStripLLT.Circular

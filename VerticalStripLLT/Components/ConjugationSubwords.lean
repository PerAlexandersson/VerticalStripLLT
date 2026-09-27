import VerticalStripLLT.Components.WordConjugation
import VerticalStripLLT.Components.CommutatorCoefficients
import VerticalStripLLT.Components.WordProductExpansion
import Mathlib.Algebra.BigOperators.Ring.List

/-! Ordered subword expansions for the finite conjugation products. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open Polynomial

noncomputable section

variable {R : Type*} [Ring R]

/-- The ascending inverse product is the product over the initial interval. -/
theorem inverseProduct_eq_range_prod (u : ℕ → R) (t : R) (n : ℕ) :
    inverseProduct u t n =
      ((List.range n).map (fun i => 1 - t * u i)).prod := by
  induction n with
  | zero => simp [inverseProduct]
  | succ n ih =>
    rw [inverseProduct_succ, ih]
    simp [List.range_succ]

/-- The descending product is the product over the reversed initial interval. -/
theorem descendingProduct_eq_reverse_range_prod (u : ℕ → R) (t : R) (n : ℕ) :
    descendingProduct u t n =
      (((List.range n).reverse).map (fun i => 1 + t * u i)).prod := by
  induction n with
  | zero => simp [descendingProduct]
  | succ n ih =>
    rw [descendingProduct_succ, ih]
    simp [List.range_succ]

private theorem list_sum_mul_sum {A : Type*} [Ring A]
    (xs ys : List A) (z : A) :
    xs.sum * z * ys.sum =
      (xs.map (fun x => (ys.map (fun y => x * z * y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    calc
      (x + xs.sum) * z * ys.sum =
          x * z * ys.sum + xs.sum * z * ys.sum := by
        simp only [add_mul, mul_assoc]
      _ = (ys.map (fun y => x * z * y)).sum +
          (xs.map (fun x => (ys.map (fun y => x * z * y)).sum)).sum := by
        have hx : (ys.map (fun y => x * z * y)).sum = x * z * ys.sum := by
          simpa only [List.map_id'] using
            (List.sum_map_mul_left ys (fun y : A => y) (x * z))
        rw [hx, ih]

/-- The inverse conjugation polynomial is an ordered double subword sum.

The left subwords come from the ascending inverse product and the right
subwords come from the descending product.  In particular, both subword
orders are inherited from their respective lists; no overlap or cardinality
reindexing is performed here.
-/
theorem inverseConjugationPolynomial_eq_double_subword_sum (u : ℕ → R) (n : ℕ) :
    inverseConjugationPolynomial u n =
      ((List.range n).sublists'.map (fun L =>
        (((List.range n).reverse).sublists'.map (fun S =>
          (L.map (fun i => -(X * C (u i)))).prod * C (u n) *
            (S.map (fun i => X * C (u i))).prod)).sum)).sum := by
  have hleft :
      ((List.range n).map (fun i => 1 - X * C (u i))).prod =
        ((List.range n).sublists'.map (fun L =>
          (L.map (fun i => -(X * C (u i)))).prod)).sum := by
    simpa only [sub_eq_add_neg] using
      (list_prod_one_add_eq_sum_subwords (R := R[X]) (List.range n)
        (fun i => -(X * C (u i))))
  have hright :
      (((List.range n).reverse).map (fun i => 1 + X * C (u i))).prod =
        (((List.range n).reverse).sublists'.map (fun S =>
          (S.map (fun i => X * C (u i))).prod)).sum := by
    exact list_prod_one_add_eq_sum_subwords (R := R[X]) ((List.range n).reverse)
      (fun i => X * C (u i))
  unfold inverseConjugationPolynomial
  rw [inverseProduct_eq_range_prod, descendingProduct_eq_reverse_range_prod, hleft, hright]
  rw [list_sum_mul_sum]
  simp only [List.map_map, Function.comp_def]

end

end VerticalStripLLT.Components

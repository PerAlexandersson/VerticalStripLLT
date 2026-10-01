import VerticalStripLLT.Components.WordProof.ConjugationSubwords
import Mathlib.Algebra.Polynomial.Coeff

/-! Coefficients of the ordered mountain subword expansion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open Polynomial

noncomputable section

variable {R : Type*} [Ring R]

private theorem list_prod_monomial_one {I : Type*} (a : I → R) (L : List I) :
    (L.map (fun i => Polynomial.monomial 1 (a i))).prod =
      Polynomial.monomial L.length ((L.map a).prod) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp [ih, Polynomial.monomial_mul_monomial, Nat.add_comm]

private theorem neg_X_mul_C_eq_monomial (u : ℕ → R) (i : ℕ) :
    -(X * C (u i)) = (Polynomial.monomial 1 (-u i) : R[X]) := by
  simp [Polynomial.X, Polynomial.monomial_neg]

private theorem X_mul_C_eq_monomial (u : ℕ → R) (i : ℕ) :
    X * C (u i) = (Polynomial.monomial 1 (u i) : R[X]) := by
  simp [Polynomial.X]

private theorem list_prod_neg_X_C (u : ℕ → R) (L : List ℕ) :
    (L.map (fun i => -(X * C (u i)))).prod =
      Polynomial.monomial L.length
        ((-1 : R) ^ L.length * (L.map u).prod) := by
  calc
    (L.map (fun i => -(X * C (u i)))).prod =
        (L.map (fun i => Polynomial.monomial 1 (-u i))).prod := by
      simp_rw [neg_X_mul_C_eq_monomial]
    _ = Polynomial.monomial L.length ((L.map (fun i => -u i)).prod) :=
      list_prod_monomial_one (fun i => -u i) L
    _ = Polynomial.monomial L.length
          ((-1 : R) ^ L.length * (L.map u).prod) := by
      congr 1
      simpa only [List.map_map, Function.comp_def, List.length_map] using
        (List.prod_map_neg (L.map u))

private theorem list_prod_X_C (u : ℕ → R) (L : List ℕ) :
    (L.map (fun i => X * C (u i))).prod =
      Polynomial.monomial L.length ((L.map u).prod) := by
  calc
    (L.map (fun i => X * C (u i))).prod =
        (L.map (fun i => Polynomial.monomial 1 (u i))).prod := by
      simp_rw [X_mul_C_eq_monomial]
    _ = Polynomial.monomial L.length ((L.map u).prod) :=
      list_prod_monomial_one u L

private theorem coeff_subword_term (u : ℕ → R) (n : ℕ)
    (L S : List ℕ) (k : ℕ) :
    (((L.map (fun i => -(X * C (u i)))).prod * C (u n) *
        (S.map (fun i => X * C (u i))).prod).coeff k) =
      if L.length + S.length = k then
        (-1 : R) ^ L.length * ((L.map u).prod * u n * (S.map u).prod)
      else 0 := by
  rw [list_prod_neg_X_C, list_prod_X_C, Polynomial.monomial_mul_C,
    Polynomial.monomial_mul_monomial]
  simp [Polynomial.coeff_monomial, mul_assoc]

/-- The degree-`k` coefficient of the double subword expansion.

Each left subword contributes one factor of `-1` per selected position, and
the coefficient vanishes unless the two selected lengths add to `k`.
-/
theorem inverseConjugationPolynomial_coeff_subword_sum (u : ℕ → R) (n k : ℕ) :
    (inverseConjugationPolynomial u n).coeff k =
      ((List.range n).sublists'.map (fun L =>
        (((List.range n).reverse).sublists'.map (fun S =>
          if L.length + S.length = k then
            (-1 : R) ^ L.length * ((L.map u).prod * u n * (S.map u).prod)
          else 0)).sum)).sum := by
  rw [inverseConjugationPolynomial_eq_double_subword_sum]
  simp_rw [Polynomial.coeff_list_sum_map, coeff_subword_term]

end

end VerticalStripLLT.Components

import VerticalStripLLT.Components.WordConjugation
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients of inverse word conjugation

The ascending inverse product conjugates a later generator to the signed
iterated commutators. The polynomial recurrence proves this without assuming
nilpotence or commutativity of the word algebra.
-/

namespace VerticalStripLLT.Components

open Polynomial

variable {R : Type*} [Ring R]

/-- The polynomial whose coefficients are the signed mountain words. -/
noncomputable def inverseConjugationPolynomial (u : ℕ → R) (n : ℕ) : R[X] :=
  inverseProduct (fun i => C (u i)) X n * C (u n) *
    descendingProduct (fun i => C (u i)) X n

private theorem polynomial_squarefree (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0) (i : ℕ) (P : R[X]) :
    C (u i) * P * C (u i) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, add_mul, hP, hQ, add_zero]
  | monomial k a =>
    rw [C_mul_monomial, monomial_mul_C, squarefree, map_zero]

private theorem polynomial_letterSum (u : ℕ → R) (n : ℕ) :
    letterSum (fun i => C (u i)) n = C (letterSum u n) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [letterSum_succ, ih, map_add]

private theorem inverse_conjugation_recurrence (u : ℕ → R) (t : R)
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n : ℕ) :
    let Q := inverseProduct u t n * u n * descendingProduct u t n
    Q + t * (letterSum u n * Q - Q * letterSum u n) = u n := by
  let A := letterSum u n
  let D := descendingProduct u t n
  let I := inverseProduct u t n
  have hDI : D * I = 1 := descendingProduct_mul_inverseProduct u t ht squarefree n
  have hID : I * D = 1 := inverseProduct_mul_descendingProduct u t ht squarefree n
  have hAD : A * D = D * A :=
    (letterSum_commute_descendingProduct u t ht squarefree triple n).eq
  have hAI : A * I = I * A := by
    calc
      A * I = I * D * A * I := by rw [hID, one_mul]
      _ = I * A * (D * I) := by rw [mul_assoc I, ← hAD]; noncomm_ring
      _ = I * A := by rw [hDI, mul_one]
  have hc : I * (A * u n - u n * A) * D =
      A * (I * u n * D) - (I * u n * D) * A := by
    rw [mul_sub, sub_mul, ← mul_assoc I A (u n), ← hAI,
      ← mul_assoc I (u n) A, mul_assoc (I * u n) A D, hAD]
    noncomm_ring
  have hconj : D * u n * I = u n + t * (A * u n - u n * A) :=
    descendingProduct_conj u t ht squarefree triple n n le_rfl
  change I * u n * D + t * (A * (I * u n * D) - (I * u n * D) * A) = u n
  calc
    I * u n * D + t * (A * (I * u n * D) - (I * u n * D) * A)
        = I * (u n + t * (A * u n - u n * A)) * D := by
          rw [← hc]
          simp only [mul_add, add_mul, mul_assoc, mul_central_left_comm ht]
    _ = I * (D * u n * I) * D := by rw [hconj]
    _ = u n := by
      calc
        I * (D * u n * I) * D = (I * D) * u n * (I * D) := by
          simp only [mul_assoc]
        _ = u n := by rw [hID, one_mul, mul_one]

/-- The inverse conjugation solves the finite polynomial commutator recurrence. -/
theorem inverseConjugationPolynomial_recurrence (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n : ℕ) :
    inverseConjugationPolynomial u n + X *
      (C (letterSum u n) * inverseConjugationPolynomial u n -
        inverseConjugationPolynomial u n * C (letterSum u n)) = C (u n) := by
  have htriple : ∀ j i k, j < i → i < k →
      C (u i) * (C (u j) * C (u k) - C (u k) * C (u j)) -
        (C (u j) * C (u k) - C (u k) * C (u j)) * C (u i) = (0 : R[X]) := by
    intro j i k hji hik
    simpa only [map_mul, map_sub, map_zero] using
      congrArg (C : R → R[X]) (triple j i k hji hik)
  simpa only [polynomial_letterSum, inverseConjugationPolynomial] using
    inverse_conjugation_recurrence (fun i => C (u i)) X Polynomial.commute_X
      (polynomial_squarefree u squarefree) htriple n

/-- The coefficient identity used for equation (4): degree `k` gives `(-1)^k ad_A^k(u n)`.
The separate ordered-subset expansion identifies these coefficients with mountain words. -/
theorem inverseConjugationPolynomial_coeff (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n k : ℕ) :
    (inverseConjugationPolynomial u n).coeff k =
      (-1 : R) ^ k * adPow (letterSum u n) (u n) k := by
  have hQ := inverseConjugationPolynomial_recurrence u squarefree triple n
  have hzero : (inverseConjugationPolynomial u n).coeff 0 = u n := by
    simpa only [coeff_add, coeff_X_mul_zero, add_zero, coeff_C_zero] using
      congrArg (fun P : R[X] => P.coeff 0) hQ
  have hsucc : ∀ r, (inverseConjugationPolynomial u n).coeff (r + 1) =
      -comm (letterSum u n) ((inverseConjugationPolynomial u n).coeff r) := by
    intro r
    have h := congrArg (fun P : R[X] => P.coeff (r + 1)) hQ
    simp only [coeff_add, coeff_X_mul, coeff_sub, coeff_C_mul, coeff_mul_C,
      coeff_C_succ] at h
    exact (add_eq_zero_iff_eq_neg).mp h
  induction k with
  | zero => simpa only [pow_zero, one_mul, adPow] using hzero
  | succ k ih =>
    have hscale : comm (letterSum u n)
        ((-1 : R) ^ k * adPow (letterSum u n) (u n) k) =
        (-1 : R) ^ k * comm (letterSum u n) (adPow (letterSum u n) (u n) k) := by
      have hcentral : letterSum u n * (-1 : R) ^ k =
          (-1 : R) ^ k * letterSum u n :=
        ((Commute.neg_one_left (letterSum u n)).pow_left k).eq.symm
      unfold comm
      rw [← mul_assoc (letterSum u n) ((-1 : R) ^ k), hcentral]
      noncomm_ring
    rw [hsucc, ih, hscale, adPow, pow_succ, mul_neg_one, neg_mul]

end VerticalStripLLT.Components

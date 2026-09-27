import VerticalStripLLT.Components.WordConjugation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Finite color products and their ordered one-peak Cauchy factorization. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

variable {R : Type*} [Ring R]

/-- The colors occur in list order; no commutativity of their word products is assumed. -/
def colorProduct (u : ℕ → R) (xs : List R) (n : ℕ) : R :=
  (xs.map fun t => descendingProduct u t n).prod

@[simp]
theorem colorProduct_nil (u : ℕ → R) (n : ℕ) : colorProduct u [] n = 1 := rfl

@[simp]
theorem colorProduct_cons (u : ℕ → R) (t : R) (xs : List R) (n : ℕ) :
    colorProduct u (t :: xs) n = descendingProduct u t n * colorProduct u xs n := rfl

@[simp]
theorem colorProduct_zero (u : ℕ → R) (xs : List R) : colorProduct u xs 0 = 1 := by
  induction xs with
  | nil => rfl
  | cons t xs ih => rw [colorProduct_cons, descendingProduct_zero, one_mul, ih]

/-- The finite prefix-conjugation sum for the new largest letter. -/
def prefixPeakCorrection (u : ℕ → R) (n : ℕ) : List R → R
  | [] => 0
  | t :: xs => t * u n +
      descendingProduct u t n * prefixPeakCorrection u n xs * inverseProduct u t n

@[simp]
theorem prefixPeakCorrection_nil (u : ℕ → R) (n : ℕ) :
    prefixPeakCorrection u n [] = 0 := rfl

@[simp]
theorem prefixPeakCorrection_cons (u : ℕ → R) (n : ℕ) (t : R) (xs : List R) :
    prefixPeakCorrection u n (t :: xs) = t * u n +
      descendingProduct u t n * prefixPeakCorrection u n xs * inverseProduct u t n := rfl

/-- Every summand of the correction contains the peak, so a second peak kills it. -/
theorem peak_mul_prefixPeakCorrection (u : ℕ → R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (xs : List R) (Y : R) : u n * Y * prefixPeakCorrection u n xs = 0 := by
  induction xs generalizing Y with
  | nil => simp
  | cons t xs ih =>
    calc
      u n * Y * prefixPeakCorrection u n (t :: xs) =
          u n * (Y * t) * u n +
            (u n * (Y * descendingProduct u t n) * prefixPeakCorrection u n xs) *
              inverseProduct u t n := by
        rw [prefixPeakCorrection_cons]
        noncomm_ring
      _ = 0 := by rw [squarefree, ih, zero_mul, add_zero]

/-- Ordered prefix conjugations factor the new peak out of the color product. -/
theorem colorProduct_succ_prefix (u : ℕ → R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (xs : List R) (hxs : ∀ t ∈ xs, ∀ Y : R, Commute t Y) :
    colorProduct u xs (n + 1) =
      (1 + prefixPeakCorrection u n xs) * colorProduct u xs n := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
    obtain ⟨ht, htail⟩ := List.forall_mem_cons.mp hxs
    let D := descendingProduct u t n
    let I := inverseProduct u t n
    let P := prefixPeakCorrection u n xs
    have hID : I * D = 1 := inverseProduct_mul_descendingProduct u t ht squarefree n
    have hzero : u n * D * P = 0 := peak_mul_prefixPeakCorrection u n squarefree xs D
    have hcross : (t * u n) * D * P = 0 := by
      calc
        (t * u n) * D * P = t * (u n * D * P) := by noncomm_ring
        _ = 0 := by rw [hzero, mul_zero]
    have htransport : (D * P * I) * D = D * P := by
      rw [mul_assoc (D * P) I D, hID, mul_one]
    have hinner : (1 + t * u n) * D * (1 + P) =
        (1 + t * u n + D * P * I) * D := by
      calc
        (1 + t * u n) * D * (1 + P) =
            (1 + t * u n) * D + D * P + (t * u n) * D * P := by noncomm_ring
        _ = (1 + t * u n) * D + D * P := by rw [hcross, add_zero]
        _ = (1 + t * u n) * D + (D * P * I) * D := by rw [htransport]
        _ = (1 + t * u n + D * P * I) * D := by noncomm_ring
    rw [colorProduct_cons, descendingProduct_succ, ih htail,
      prefixPeakCorrection_cons, colorProduct_cons]
    simpa only [D, I, P, add_assoc, mul_assoc] using
      congrArg (fun Z => Z * colorProduct u xs n) hinner

/-- Finite elementary coefficients of the scalar list, defined by deletion of its head. -/
def elementaryScalar : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | t :: xs, k + 1 => elementaryScalar xs (k + 1) + t * elementaryScalar xs k

@[simp]
theorem elementaryScalar_zero (xs : List R) : elementaryScalar xs 0 = 1 := by
  cases xs <;> rfl

@[simp]
theorem elementaryScalar_nil_succ (k : ℕ) : elementaryScalar ([] : List R) (k + 1) = 0 := rfl

@[simp]
theorem elementaryScalar_cons_succ (t : R) (xs : List R) (k : ℕ) :
    elementaryScalar (t :: xs) (k + 1) =
      elementaryScalar xs (k + 1) + t * elementaryScalar xs k := rfl

/-- Degrees greater than the number of colors have zero elementary coefficient. -/
theorem elementaryScalar_eq_zero_of_length_lt (xs : List R) (k : ℕ)
    (hk : xs.length < k) : elementaryScalar xs k = 0 := by
  induction xs generalizing k with
  | nil => cases k <;> simp_all [elementaryScalar]
  | cons t xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hk' : xs.length < k := by simpa using hk
      rw [elementaryScalar_cons_succ, ih (k + 1) (by lia), ih k hk']
      simp

/-- Elementary coefficients remain central when their scalar entries are central. -/
theorem elementaryScalar_commute (xs : List R)
    (hxs : ∀ t ∈ xs, ∀ Y : R, Commute t Y) (k : ℕ) (Y : R) :
    Commute (elementaryScalar xs k) Y := by
  induction xs generalizing k with
  | nil => cases k <;> simp [elementaryScalar]
  | cons t xs ih =>
    obtain ⟨ht, htail⟩ := List.forall_mem_cons.mp hxs
    cases k with
    | zero => exact Commute.one_left Y
    | succ k =>
      exact (ih htail (k + 1)).add_left ((ht Y).mul_left (ih htail k))

/-- The prefix sum is the finite elementary-weighted sum of iterated commutators.
The bound is the number of colors, so no infinite series or nilpotence bound is used. -/
theorem prefixPeakCorrection_eq_sum (u : ℕ → R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (xs : List R) (hxs : ∀ t ∈ xs, ∀ Y : R, Commute t Y) :
    prefixPeakCorrection u n xs =
      ∑ k ∈ Finset.range xs.length,
        elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
    obtain ⟨ht, htail⟩ := List.forall_mem_cons.mp hxs
    let A := letterSum u n
    let D := descendingProduct u t n
    let I := inverseProduct u t n
    have hconj : D *
        (∑ k ∈ Finset.range xs.length, elementaryScalar xs (k + 1) * adPow A (u n) k) * I =
        ∑ k ∈ Finset.range xs.length,
          elementaryScalar xs (k + 1) * (adPow A (u n) k + t * adPow A (u n) (k + 1)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      have hc := elementaryScalar_commute xs htail (k + 1) D
      calc
        D * (elementaryScalar xs (k + 1) * adPow A (u n) k) * I =
            elementaryScalar xs (k + 1) * (D * adPow A (u n) k * I) := by
          rw [← mul_assoc D, hc.eq.symm]
          simp only [mul_assoc]
        _ = _ := by
          rw [descendingProduct_conj_adPow u t ht squarefree triple n n le_rfl k]
    have hterm (k : ℕ) :
        elementaryScalar xs (k + 1) *
            (adPow A (u n) k + t * adPow A (u n) (k + 1)) =
          elementaryScalar xs (k + 1) * adPow A (u n) k +
            t * elementaryScalar xs (k + 1) * adPow A (u n) (k + 1) := by
      rw [mul_add, ← mul_assoc, (ht (elementaryScalar xs (k + 1))).eq.symm]
    have htop : elementaryScalar xs (xs.length + 1) = 0 :=
      elementaryScalar_eq_zero_of_length_lt xs _ (by lia)
    rw [prefixPeakCorrection_cons, ih htail]
    change t * u n + D *
        (∑ k ∈ Finset.range xs.length, elementaryScalar xs (k + 1) * adPow A (u n) k) * I = _
    rw [hconj]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp only [List.length_cons, elementaryScalar_cons_succ, add_mul]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_range_succ
      (fun k => elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k)]
    rw [htop, zero_mul, add_zero]
    rw [Finset.sum_range_succ'
      (fun k => t * elementaryScalar xs k * adPow (letterSum u n) (u n) k)]
    simp only [elementaryScalar_zero, mul_one, adPow]
    dsimp only [A]
    noncomm_ring

/-- The finite one-peak Cauchy factor step, with its order of multiplication fixed. -/
theorem colorProduct_succ_cauchy (u : ℕ → R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (xs : List R) (hxs : ∀ t ∈ xs, ∀ Y : R, Commute t Y) :
    colorProduct u xs (n + 1) =
      (1 + ∑ k ∈ Finset.range xs.length,
        elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) *
          colorProduct u xs n := by
  rw [colorProduct_succ_prefix u n squarefree xs hxs,
    prefixPeakCorrection_eq_sum u n squarefree triple xs hxs]

/-- The ordered finite product of the successive peak factors. -/
def cauchyProduct (u : ℕ → R) (xs : List R) : ℕ → R
  | 0 => 1
  | n + 1 =>
      (1 + ∑ k ∈ Finset.range xs.length,
        elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) *
          cauchyProduct u xs n

/-- Iterating the one-peak step gives the finite ordered Cauchy factorization. -/
theorem colorProduct_eq_cauchyProduct (u : ℕ → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (xs : List R) (hxs : ∀ t ∈ xs, ∀ Y : R, Commute t Y) (n : ℕ) :
    colorProduct u xs n = cauchyProduct u xs n := by
  induction n with
  | zero => exact colorProduct_zero u xs
  | succ n ih =>
    rw [colorProduct_succ_cauchy u n squarefree triple xs hxs, ih]
    rfl

end VerticalStripLLT.Components

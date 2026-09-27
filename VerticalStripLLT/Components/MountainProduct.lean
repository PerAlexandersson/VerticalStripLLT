import VerticalStripLLT.Components.MountainCauchy

/-! The ordered finite expansion of the Cauchy product into mountain choices. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {R : Type*} [Ring R]

/-- The ordered word carried by a mountain with peak `n`. -/
def mountainWord (u : ℕ → R) (n : ℕ) (B T : Finset ℕ) : R :=
  ((incWord (B \ T)).map u).prod * u n * ((decWord T).map u).prod

/-- The signed scalar weight carried by one mountain choice. -/
def mountainTerm (u : ℕ → R) (xs : List R) (n : ℕ)
    (B T : Finset ℕ) : R :=
  elementaryScalar xs (B.card + 1) * (-1 : R) ^ T.card * mountainWord u n B T

/--
The recursive finite choice expansion.  At stage `n`, the first summand chooses
no mountain at the new peak; the other summands choose `B` and `T ⊆ B` and put
that mountain on the left of the previously chosen ordered product.
-/
def mountainProduct (u : ℕ → R) (xs : List R) : ℕ → R
  | 0 => 1
  | n + 1 =>
      mountainProduct u xs n +
        ∑ B ∈ (Finset.range n).powerset,
          ∑ T ∈ B.powerset,
            mountainTerm u xs n B T * mountainProduct u xs n

@[simp]
theorem mountainProduct_zero (u : ℕ → R) (xs : List R) :
    mountainProduct u xs 0 = 1 := rfl

theorem mountainProduct_succ (u : ℕ → R) (xs : List R) (n : ℕ) :
    mountainProduct u xs (n + 1) =
      mountainProduct u xs n +
        ∑ B ∈ (Finset.range n).powerset,
          ∑ T ∈ B.powerset,
            mountainTerm u xs n B T * mountainProduct u xs n := rfl

/-- The one-step peak sum is exactly the finite sum of mountain choices. -/
theorem cauchyPeak_eq_mountainChoices (u : ℕ → R) (xs : List R) (n : ℕ)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) -
        (u j * u k - u k * u j) * u i = 0) :
    (∑ k ∈ Finset.range xs.length,
      elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) =
      ∑ B ∈ (Finset.range n).powerset,
        ∑ T ∈ B.powerset, mountainTerm u xs n B T := by
  rw [elementary_adPow_eq_powerset_mountain u n squarefree triple xs]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [mountainTerm, mountainWord, mul_assoc]

/-- The finite ordered Cauchy product is the mountain-choice expansion. -/
theorem cauchyProduct_eq_mountainProduct (u : ℕ → R) (xs : List R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) -
        (u j * u k - u k * u j) * u i = 0)
    (n : ℕ) :
    cauchyProduct u xs n = mountainProduct u xs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (1 + ∑ k ∈ Finset.range xs.length,
          elementaryScalar xs (k + 1) * adPow (letterSum u n) (u n) k) *
            cauchyProduct u xs n =
        mountainProduct u xs n +
          ∑ B ∈ (Finset.range n).powerset,
            ∑ T ∈ B.powerset,
              mountainTerm u xs n B T * mountainProduct u xs n
      rw [ih, cauchyPeak_eq_mountainChoices u xs n squarefree triple]
      simp only [add_mul, one_mul, Finset.sum_mul]

end

end VerticalStripLLT.Components

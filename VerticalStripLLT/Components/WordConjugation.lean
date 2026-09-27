import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing

/-!
# Finite squarefree word conjugation

Algebraic lemmas about the products `∏ (1 + t * u i)` (descending) and
`∏ (1 - t * u i)` (ascending) in an arbitrary ring, where `t` is central,
every generator `u i` is "squarefree" (`u i * Y * u i = 0`) and the
generators satisfy the triple commutator relation for `j < i < k`.
-/

namespace VerticalStripLLT.Components

variable {R : Type*} [Ring R]

/-- Local commutator `[a, b] = a * b - b * a` (avoids Lie instance issues). -/
def comm (a b : R) : R := a * b - b * a

/-- `letterSum u n = u 0 + u 1 + ⋯ + u (n-1)`. -/
def letterSum (u : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => letterSum u n + u n

/-- `descendingProduct u t n = (1 + t u(n-1)) ⋯ (1 + t u 0)`. -/
def descendingProduct (u : ℕ → R) (t : R) : ℕ → R
  | 0 => 1
  | n + 1 => (1 + t * u n) * descendingProduct u t n

/-- `inverseProduct u t n = (1 - t u 0) ⋯ (1 - t u(n-1))`. -/
def inverseProduct (u : ℕ → R) (t : R) : ℕ → R
  | 0 => 1
  | n + 1 => inverseProduct u t n * (1 - t * u n)

@[simp] theorem letterSum_zero (u : ℕ → R) : letterSum u 0 = 0 := rfl
@[simp] theorem letterSum_succ (u : ℕ → R) (n : ℕ) :
    letterSum u (n + 1) = letterSum u n + u n := rfl
@[simp] theorem descendingProduct_zero (u : ℕ → R) (t : R) :
    descendingProduct u t 0 = 1 := rfl
@[simp] theorem descendingProduct_succ (u : ℕ → R) (t : R) (n : ℕ) :
    descendingProduct u t (n + 1) = (1 + t * u n) * descendingProduct u t n := rfl
@[simp] theorem inverseProduct_zero (u : ℕ → R) (t : R) :
    inverseProduct u t 0 = 1 := rfl
@[simp] theorem inverseProduct_succ (u : ℕ → R) (t : R) (n : ℕ) :
    inverseProduct u t (n + 1) = inverseProduct u t n * (1 - t * u n) := rfl

/-- Move a central scalar past the left factor of an associated product. -/
theorem mul_central_left_comm {t : R} (ht : ∀ x : R, Commute t x) (x c : R) :
    x * (t * c) = t * (x * c) := by
  exact ((ht x).left_comm c).symm

section

variable (u : ℕ → R) (t : R)

/-- Conjugation by `1 + t * a` for central `t` and `a * Y * a = 0`. -/
private theorem conj_one_add_central {a Y : R} (ht : ∀ x : R, Commute t x)
    (h : a * Y * a = 0) :
    (1 + t * a) * Y * (1 - t * a) = Y + t * (a * Y - Y * a) := by
  have h' : a * (Y * a) = 0 := by rw [← mul_assoc, h]
  simp only [mul_add, add_mul, mul_sub, mul_one, one_mul, mul_assoc,
    mul_central_left_comm ht, h', mul_zero]
  noncomm_ring

private theorem triple_letterSum
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (i k : ℕ) (hik : i < k) (m : ℕ) (hm : m ≤ i) :
    u i * (letterSum u m * u k - u k * letterSum u m)
      - (letterSum u m * u k - u k * letterSum u m) * u i = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u i * (letterSum u (m + 1) * u k - u k * letterSum u (m + 1))
        - (letterSum u (m + 1) * u k - u k * letterSum u (m + 1)) * u i
        = (u i * (letterSum u m * u k - u k * letterSum u m)
            - (letterSum u m * u k - u k * letterSum u m) * u i)
          + (u i * (u m * u k - u k * u m) - (u m * u k - u k * u m) * u i) := by
      simp only [letterSum_succ]; noncomm_ring
    rw [e, ih (by lia), triple m i k (by lia) hik, add_zero]

/-- `descendingProduct u t n * inverseProduct u t n = 1`. -/
theorem descendingProduct_mul_inverseProduct
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0) (n : ℕ) :
    descendingProduct u t n * inverseProduct u t n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc descendingProduct u t (n + 1) * inverseProduct u t (n + 1)
        = (1 + t * u n) * (descendingProduct u t n * inverseProduct u t n) * (1 - t * u n) := by
          simp only [descendingProduct_succ, inverseProduct_succ, mul_assoc]
      _ = 1 := by
          rw [ih, conj_one_add_central t ht (squarefree n 1)]
          simp

/-- `inverseProduct u t n * descendingProduct u t n = 1`. -/
theorem inverseProduct_mul_descendingProduct
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0) (n : ℕ) :
    inverseProduct u t n * descendingProduct u t n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hvv : u n * u n = 0 := by simpa using squarefree n 1
    calc inverseProduct u t (n + 1) * descendingProduct u t (n + 1)
        = inverseProduct u t n * ((1 - t * u n) * (1 + t * u n)) * descendingProduct u t n := by
          simp only [descendingProduct_succ, inverseProduct_succ, mul_assoc]
      _ = inverseProduct u t n * (1 - t * (t * (u n * u n))) * descendingProduct u t n := by
          congr 2
          simp only [mul_add, mul_sub, sub_mul, mul_one, one_mul, mul_assoc,
            mul_central_left_comm ht]
          noncomm_ring
      _ = 1 := by rw [hvv, mul_zero, mul_zero, sub_zero, mul_one, ih]

/-- conjugation of a later letter `u k` (`n ≤ k`) by the descending product. -/
theorem descendingProduct_conj
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n k : ℕ) (hk : n ≤ k) :
    descendingProduct u t n * u k * inverseProduct u t n
      = u k + t * (letterSum u n * u k - u k * letterSum u n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set C := letterSum u n * u k - u k * letterSum u n with hC
    set Y := u k + t * C with hY
    have hC0 : u n * C - C * u n = 0 := triple_letterSum u triple n k (by lia) n le_rfl
    calc descendingProduct u t (n + 1) * u k * inverseProduct u t (n + 1)
        = (1 + t * u n) * (descendingProduct u t n * u k * inverseProduct u t n)
            * (1 - t * u n) := by
          simp only [descendingProduct_succ, inverseProduct_succ, mul_assoc]
      _ = (1 + t * u n) * Y * (1 - t * u n) := by rw [ih (by lia)]
      _ = Y + t * (u n * Y - Y * u n) := conj_one_add_central t ht (squarefree n Y)
      _ = Y + t * ((u n * u k - u k * u n) + t * (u n * C - C * u n)) := by
          congr 2
          rw [hY]
          simp only [mul_add, add_mul, mul_sub, mul_assoc, mul_central_left_comm ht]
          noncomm_ring
      _ = u k + t * (letterSum u (n + 1) * u k - u k * letterSum u (n + 1)) := by
          rw [hC0, mul_zero, add_zero, hY, hC, letterSum_succ]
          noncomm_ring

/-- the letter sum commutes with the descending product. -/
theorem letterSum_commute_descendingProduct
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n : ℕ) :
    Commute (letterSum u n) (descendingProduct u t n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set A := letterSum u n with hA
    set D := descendingProduct u t n with hD
    set v := u n with hv
    have hDA : D * A = A * D := ih.eq.symm
    have hconj : D * v * inverseProduct u t n = v + t * (A * v - v * A) :=
      descendingProduct_conj u t ht squarefree triple n n le_rfl
    have hDv : D * v = (v + t * (A * v - v * A)) * D := by
      rw [← hconj, mul_assoc _ (inverseProduct u t n),
        inverseProduct_mul_descendingProduct u t ht squarefree n, mul_one]
    have hvv : ∀ X, v * (v * X) = 0 := fun X => by
      rw [← mul_assoc, show v * v = 0 by simpa using squarefree n 1, zero_mul]
    have hvAv : ∀ X, v * (A * (v * X)) = 0 := fun X => by
      rw [← mul_assoc, ← mul_assoc, squarefree n A, zero_mul]
    show (letterSum u (n + 1)) * descendingProduct u t (n + 1)
      = descendingProduct u t (n + 1) * letterSum u (n + 1)
    rw [letterSum_succ, descendingProduct_succ, ← hA, ← hD, ← hv]
    simp only [add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_assoc,
      mul_central_left_comm ht, hDA, hDv, hvv, hvAv, mul_zero]
    noncomm_ring

/-- Iterated commutator `ad_A^r(Y)`, built from the local commutator `comm`. -/
def adPow (A Y : R) : ℕ → R
  | 0 => Y
  | r + 1 => comm A (adPow A Y r)

/-- for `n ≤ k`, conjugation by `descendingProduct u t n` sends
`ad_A^r (u k)` (with `A = letterSum u n`) to `ad_A^r (u k) + t * ad_A^(r+1) (u k)`. -/
theorem descendingProduct_conj_adPow
    (ht : ∀ x : R, Commute t x)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (triple : ∀ j i k, j < i → i < k →
      u i * (u j * u k - u k * u j) - (u j * u k - u k * u j) * u i = 0)
    (n k : ℕ) (hk : n ≤ k) (r : ℕ) :
    descendingProduct u t n * adPow (letterSum u n) (u k) r * inverseProduct u t n
      = adPow (letterSum u n) (u k) r + t * adPow (letterSum u n) (u k) (r + 1) := by
  set A := letterSum u n with hA
  set D := descendingProduct u t n with hD
  set I := inverseProduct u t n with hI
  have hDI : D * I = 1 := descendingProduct_mul_inverseProduct u t ht squarefree n
  have hID : I * D = 1 := inverseProduct_mul_descendingProduct u t ht squarefree n
  have hDA : D * A = A * D :=
    (letterSum_commute_descendingProduct u t ht squarefree triple n).eq.symm
  have hAI : A * I = I * A := by
    calc A * I = I * D * A * I := by rw [hID, one_mul]
      _ = I * A * (D * I) := by rw [mul_assoc I, hDA]; noncomm_ring
      _ = I * A := by rw [hDI, mul_one]
  induction r with
  | zero =>
    simp only [adPow, comm]
    exact descendingProduct_conj u t ht squarefree triple n k hk
  | succ r ih =>
    set X := adPow A (u k) r with hX
    have e : D * adPow A (u k) (r + 1) * I = A * (D * X * I) - (D * X * I) * A := by
      simp only [adPow, comm, ← hX]
      rw [mul_sub, sub_mul, ← mul_assoc D A X, hDA, ← mul_assoc D X A, mul_assoc (D * X) A I, hAI]
      noncomm_ring
    rw [e, ih]
    simp only [adPow, comm, ← hX]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_central_left_comm ht]
    noncomm_ring

end

end VerticalStripLLT.Components

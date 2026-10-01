import VerticalStripLLT.Components.WordProof.BlockExtractor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! A literal finite scan for ordered mountain continuations. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K]

/--
At stage `k`, the scan either skips the new letter or prepends one mountain
whose peak is `k` to the continuation.  The `if` keeps the definition valid
when the scan has passed the finite alphabet.
-/
def mountainScan (a : ℕ → K) (n : ℕ) :
    ℕ → (List (Fin n) → K) → K
  | 0 => fun f => f []
  | k + 1 => fun f =>
      mountainScan a n k f +
        if hk : k < n then
          ∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset,
            ∑ T ∈ B.powerset,
              a (B.card + 1) * (-1 : K) ^ T.card *
                mountainScan a n k
                  (fun w => f (blockWord (insert ⟨k, hk⟩ B) T ++ w))
        else 0

@[simp]
theorem mountainScan_zero (a : ℕ → K) (n : ℕ)
    (f : List (Fin n) → K) : mountainScan a n 0 f = f [] := rfl

/-- The literal scan recursion below the alphabet size. -/
theorem mountainScan_succ_of_lt (a : ℕ → K) {n k : ℕ} (hk : k < n)
    (f : List (Fin n) → K) :
    mountainScan a n (k + 1) f = mountainScan a n k f +
      ∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset, ∑ T ∈ B.powerset,
        a (B.card + 1) * (-1 : K) ^ T.card *
          mountainScan a n k (fun w => f (blockWord (insert ⟨k, hk⟩ B) T ++ w)) := by
  simp only [mountainScan, dite_eq_left hk]

theorem mountainScan_congr (a : ℕ → K) (n k : ℕ)
    {f g : List (Fin n) → K} (hfg : ∀ w, f w = g w) :
    mountainScan a n k f = mountainScan a n k g := by
  exact congrArg (mountainScan a n k) (funext hfg)

theorem mountainScan_add (a : ℕ → K) (n k : ℕ)
    (f g : List (Fin n) → K) :
    mountainScan a n k (fun w => f w + g w) =
      mountainScan a n k f + mountainScan a n k g := by
  induction k generalizing f g with
  | zero => simp [mountainScan]
  | succ k ih =>
      simp only [mountainScan]
      split_ifs with hk
      · simp_rw [ih]
        simp only [Finset.sum_add_distrib, mul_add]
        ring
      · rw [ih]
        simp only [add_zero]

theorem mountainScan_mul (a : ℕ → K) (n k : ℕ) (r : K)
    (f : List (Fin n) → K) :
    mountainScan a n k (fun w => r * f w) =
      r * mountainScan a n k f := by
  induction k generalizing f with
  | zero => simp [mountainScan]
  | succ k ih =>
      simp only [mountainScan]
      split_ifs with hk
      · simp_rw [ih]
        simp only [mul_add, Finset.mul_sum, mul_left_comm, mul_assoc]
      · rw [ih]
        simp only [add_zero]

theorem mountainScan_mul_right (a : ℕ → K) (n k : ℕ) (r : K)
    (f : List (Fin n) → K) :
    mountainScan a n k (fun w => f w * r) =
      mountainScan a n k f * r := by
  simpa [mul_comm] using mountainScan_mul a n k r f

theorem mountainScan_zero_continuation (a : ℕ → K) (n k : ℕ) :
    mountainScan a n k (fun _ => 0) = 0 := by
  simpa using (mountainScan_mul a n k (0 : K) (fun _ => 1))

theorem mountainScan_sum {I : Type*} (a : ℕ → K) (n k : ℕ)
    (s : Finset I) (f : I → List (Fin n) → K) :
    mountainScan a n k (fun w => ∑ i ∈ s, f i w) =
      ∑ i ∈ s, mountainScan a n k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mountainScan_zero_continuation]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mountainScan_add, ih]

end

end VerticalStripLLT.Components

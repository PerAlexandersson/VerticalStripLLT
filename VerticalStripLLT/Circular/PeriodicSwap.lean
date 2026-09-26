import Mathlib.Data.Int.ModEq
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Periodic adjacent swaps. Aristotle candidate, locally ported; see docs/ARISTOTLE.md. -/

namespace VerticalStripLLT.Circular

def periodicSwap (n p z : ℤ) : ℤ :=
  if (z - p) % n = 0 then z + 1 else
    if (z - p) % n = 1 then z - 1 else z

theorem periodicSwap_involutive (n p : ℤ) (hn : 2 ≤ n) :
    Function.Involutive (periodicSwap n p) := by
  intro z
  have h1 : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by lia)
  unfold periodicSwap
  by_cases h0 : (z - p) % n = 0
  · have e : (z + 1 - p) % n = 1 := by
      rw [show z + 1 - p = (z - p) + 1 by ring, ← Int.emod_add_emod, h0, zero_add, h1]
    simp [h0, e]
  · by_cases h1' : (z - p) % n = 1
    · have e : (z - 1 - p) % n = 0 := by
        rw [show z - 1 - p = (z - p) - 1 by ring, Int.sub_emod, h1', h1, sub_self,
          Int.zero_emod]
      simp [h1', e]
    · simp [h0, h1']

theorem periodicSwap_translate (n p z k : ℤ) (_hn : 2 ≤ n) :
    periodicSwap n p (z + n * k) = periodicSwap n p z + n * k := by
  have e : (z + n * k - p) % n = (z - p) % n := by
    rw [show z + n * k - p = (z - p) + n * k by ring, Int.add_mul_emod_self_left]
  unfold periodicSwap
  rw [e]
  split_ifs <;> ring

theorem periodicSwap_strictMonoOn (n p : ℤ) (hn : 2 ≤ n) (S : Set ℤ)
    (hS : ∀ k : ℤ, ¬ (p + n * k ∈ S ∧ p + 1 + n * k ∈ S)) :
    StrictMonoOn (periodicSwap n p) S := by
  intro u hu v hv huv
  have hmod : ∀ c : ℤ, (v - p) = (u - p) + c → (v - p) % n = ((u - p) % n + c) % n := by
    intro c hc
    rw [Int.emod_add_emod, hc]
  have h1 : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by lia)
  have h2 : (2 : ℤ) % n ≠ 1 := by
    rcases eq_or_lt_of_le hn with h | h
    · subst h; decide
    · rw [Int.emod_eq_of_lt (by lia) h]; lia
  have hr0 := Int.emod_nonneg (u - p) (by lia : n ≠ 0)
  have hr1 := Int.emod_lt_of_pos (u - p) (by lia : 0 < n)
  obtain ⟨k, hk⟩ : ∃ k, u - p = n * k + (u - p) % n := ⟨_, (Int.mul_ediv_add_emod _ _).symm⟩
  unfold periodicSwap
  split_ifs with a b c d e f g h <;> try lia
  · -- ru = 0, rv = 1
    by_contra hc
    rcases (show v = u + 1 ∨ v = u + 2 by lia) with hv' | hv'
    · exact hS k ⟨by convert hu using 1; lia, by convert hv using 1; lia⟩
    · rw [hmod 2 (by lia), a, zero_add] at c; exact h2 c
  · -- ru = 0, rv other
    by_contra hc
    rw [hmod 1 (by lia), a, zero_add, h1] at c; exact c rfl
  · -- ru other, rv = 1
    by_contra hc
    rw [hmod 1 (by lia)] at h
    rcases (show (u - p) % n + 1 < n ∨ (u - p) % n + 1 = n by lia) with hl | hl
    · rw [Int.emod_eq_of_lt (by lia) hl] at h; lia
    · rw [hl, Int.emod_self] at h; lia

end VerticalStripLLT.Circular

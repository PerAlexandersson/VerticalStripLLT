import VerticalStripLLT.Components.DiagramProof.Foundation.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Linarith

/-! An order embedding enumerating any interval of `Fin n`. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- Every interval `[lo, hi]` of `Fin n` is enumerated by an order embedding. -/
theorem exists_interval_orderEmbedding {n : ℕ} (lo hi : Fin n) (hle : lo ≤ hi) :
    ∃ k, ∃ ι : Fin (k + 1) ↪o Fin n,
      ι 0 = lo ∧ ι (Fin.last k) = hi ∧
        ∀ v, (∃ i, ι i = v) ↔ lo ≤ v ∧ v ≤ hi := by
  let k : ℕ := hi.val - lo.val
  have hlohi : lo.val ≤ hi.val := hle
  have hsum : lo.val + k = hi.val := by
    exact Nat.add_sub_of_le hlohi
  let f : Fin (k + 1) → Fin n := fun i =>
    ⟨lo.val + i.val, by
      have hi' : lo.val + i.val ≤ hi.val := by
        rw [← hsum]
        exact Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) _
      exact lt_of_le_of_lt hi' hi.isLt⟩
  let ι : Fin (k + 1) ↪o Fin n :=
    OrderEmbedding.ofStrictMono f (by
      intro a b hab
      change lo.val + a.val < lo.val + b.val
      exact Nat.add_lt_add_left hab _)
  refine ⟨k, ι, ?_, ?_, ?_⟩
  · apply Fin.ext
    change lo.val + 0 = lo.val
    exact Nat.add_zero _
  · apply Fin.ext
    change lo.val + k = hi.val
    exact hsum
  · intro v
    constructor
    · rintro ⟨i, rfl⟩
      constructor
      · exact Nat.le_add_right lo.val i.val
      · change lo.val + i.val ≤ hi.val
        rw [← hsum]
        exact Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) _
    · rintro ⟨hlov, hvhi⟩
      have hlov' : lo.val ≤ v.val := hlov
      have hvhi' : v.val ≤ hi.val := hvhi
      let i : Fin (k + 1) :=
        ⟨v.val - lo.val, by
          have : v.val - lo.val < k + 1 := by lia
          exact this⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      change lo.val + (v.val - lo.val) = v.val
      exact Nat.add_sub_of_le hlov'

end VerticalStripLLT.Circular.DiagramProof

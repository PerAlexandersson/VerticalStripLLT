import VerticalStripLLT.Components.DiagramProof.Foundation.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Linarith

/-! The ordered core consisting of `0, ..., c` together with a later vertex `e`. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- The order embedding enumerating `0, ..., c` followed by `e`. -/
def lastCliqueEmbed {n : ℕ} (c e : Fin n) (hce : c < e) :
    Fin (c.val + 2) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i => if hi : i.val ≤ c.val then
      ⟨i.val, lt_of_le_of_lt hi c.isLt⟩
    else e)
    (by
      intro i j hij
      by_cases hi : i.val ≤ c.val
      · by_cases hj : j.val ≤ c.val
        · simp only [hi, hj, dite_true]
          exact hij
        · simp only [hi, hj, dite_true, dite_false]
          change i.val < e.val
          exact hi.trans_lt hce
      · have hji : j.val ≤ c.val := by
          have hij' : i.val < j.val := hij
          have hjlt : j.val < c.val + 2 := j.isLt
          by_contra hjnot
          have hi' : c.val + 1 ≤ i.val := by lia
          lia
        exact (hi (by lia)).elim)

@[simp]
theorem lastCliqueEmbed_of_le {n : ℕ} (c e : Fin n) (hce : c < e)
    (i : Fin (c.val + 2)) (hi : i.val ≤ c.val) :
    lastCliqueEmbed c e hce i = ⟨i.val, lt_of_le_of_lt hi c.isLt⟩ := by
  simp [lastCliqueEmbed, OrderEmbedding.ofStrictMono, hi]

@[simp]
theorem lastCliqueEmbed_last {n : ℕ} (c e : Fin n) (hce : c < e) :
    lastCliqueEmbed c e hce (Fin.last (c.val + 1)) = e := by
  simp [lastCliqueEmbed, OrderEmbedding.ofStrictMono]

/-- The image of `lastCliqueEmbed c e` is `0, ..., c` together with `e`. -/
theorem lastCliqueEmbed_image {n : ℕ} (c e : Fin n) (hce : c < e) (v : Fin n) :
    (∃ i, lastCliqueEmbed c e hce i = v) ↔
      v.val ≤ c.val ∨ v = e := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val ≤ c.val
    · left
      rw [lastCliqueEmbed_of_le c e hce i hi]
      exact hi
    · right
      simp [lastCliqueEmbed, OrderEmbedding.ofStrictMono, hi]
  · intro hv
    rcases hv with hv | hv
    · let i : Fin (c.val + 2) := ⟨v.val, by lia⟩
      refine ⟨i, ?_⟩
      rw [lastCliqueEmbed_of_le c e hce i hv]
    · exact ⟨Fin.last (c.val + 1), (lastCliqueEmbed_last c e hce).trans hv.symm⟩

end

end VerticalStripLLT.Circular.DiagramProof

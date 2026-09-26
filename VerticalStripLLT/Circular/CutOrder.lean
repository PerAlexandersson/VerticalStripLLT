import VerticalStripLLT.Circular.Diagram
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-! Offset geometry for a circular area sequence and a chosen cut. -/

namespace VerticalStripLLT.Circular

namespace CircularArea

variable {n : ℕ} (A : CircularArea n)

/-- Move a vertex forward by a natural number of cyclic positions. -/
def atOffset (c : Fin n) (k : ℕ) : Fin n :=
  ⟨(c.val + k) % n, Nat.mod_lt _ A.positive⟩

@[simp] theorem atOffset_zero (c : Fin n) : A.atOffset c 0 = c := by
  apply Fin.ext
  simp [atOffset, Nat.mod_eq_of_lt c.isLt]

@[simp] theorem atOffset_succ (c : Fin n) (k : ℕ) :
    A.atOffset c (k + 1) = A.next (A.atOffset c k) := by
  apply Fin.ext
  simp [atOffset, CircularArea.next, Nat.add_assoc]

theorem area_atOffset_le (c : Fin n) (k : ℕ) :
    A.area (A.atOffset c k) ≤ A.area c + k := by
  induction k with
  | zero => simp [A.atOffset_zero]
  | succ k ih =>
    calc
      A.area (A.atOffset c (k + 1)) =
          A.area (A.next (A.atOffset c k)) := congrArg A.area (A.atOffset_succ c k)
      _ ≤ A.area (A.atOffset c k) + 1 := A.cyclic _
      _ ≤ A.area c + k + 1 := by lia

theorem area_atOffset_le_of_zero (c : Fin n) (hc : A.area c = 0) (k : ℕ) :
    A.area (A.atOffset c k) ≤ k := by
  simpa [hc] using A.area_atOffset_le c k

theorem atOffset_fin_injective (c : Fin n) :
    Function.Injective (fun k : Fin n => A.atOffset c k.val) := by
  intro a b hab
  have hm : c.val + a.val ≡ c.val + b.val [MOD n] := by
    change (c.val + a.val) % n = (c.val + b.val) % n
    exact congrArg Fin.val hab
  have hm' : a.val ≡ b.val [MOD n] := Nat.ModEq.add_left_cancel' c.val hm
  exact Fin.ext (hm'.eq_of_lt_of_lt a.isLt b.isLt)

end CircularArea
end VerticalStripLLT.Circular

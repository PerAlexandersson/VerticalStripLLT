import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Linarith

/-! Arithmetic coordinates and the permutation reversing residue columns in `Fin N`. -/

namespace VerticalStripLLT.Circular

/-- Number of elements of `Fin N` congruent to `c` modulo `j`, for a canonical
column representative `c < j`. -/
def colLen (N j c : ℕ) : ℕ := (N + j - 1 - c) / j

/-- The value obtained by reversing the `j`-column containing `c + j*h`. -/
def columnReverseIndex (N j c h : ℕ) : ℕ :=
  c + j * (colLen N j c - 1 - h)

/-- The formula never changes a column residue. -/
theorem columnReverseIndex_mod (N j c h : ℕ) (_hj : 0 < j) :
    columnReverseIndex N j c h % j = c % j := by
  simp [columnReverseIndex, Nat.add_mod]

/-- In canonical coordinates the reversed value has the same residue. -/
theorem columnReverseIndex_mod_eq (N j c h : ℕ) (hc : c < j) :
    columnReverseIndex N j c h % j = c := by
  rw [columnReverseIndex_mod N j c h (by lia), Nat.mod_eq_of_lt hc]

/-- Reflection is involutive for every row in its finite column. -/
theorem columnReverseIndex_involutive_formula (N j c h : ℕ)
    (hh : h ≤ colLen N j c - 1) :
    columnReverseIndex N j c (colLen N j c - 1 - h) = c + j * h := by
  simp [columnReverseIndex, Nat.sub_sub_self hh]

/-- Exactly the valid row coordinates of a nonempty column. -/
theorem lt_colLen_iff {N j c h : ℕ} (hj : 0 < j) (hc : c < N) :
    h < colLen N j c ↔ c + j * h < N := by
  rw [colLen, Nat.lt_div_iff_mul_lt hj]
  rw [show N + j - 1 - c - (j - 1) = N - c by lia, Nat.mul_comm h j]
  lia

theorem columnReverseIndex_lt {N j c h : ℕ} (hj : 0 < j)
    (hh : c + j * h < N) : columnReverseIndex N j c h < N := by
  have hc : c < N := by lia
  have hrow := (lt_colLen_iff hj hc).mpr hh
  exact (lt_colLen_iff hj hc).mp (by lia)

theorem columnReverseIndex_div {N j c h : ℕ} (hj : 0 < j) (hc : c < j) :
    columnReverseIndex N j c h / j = colLen N j c - 1 - h := by
  simp [columnReverseIndex, Nat.add_mul_div_left _ _ hj, Nat.div_eq_of_lt hc]

/-- Reverse all residue columns, as an actual bounded index map. -/
def columnReverseFin (N j : ℕ) (hj : 0 < j) (a : Fin N) : Fin N :=
  ⟨columnReverseIndex N j (a.val % j) (a.val / j),
    columnReverseIndex_lt hj (by rw [Nat.mod_add_div]; exact a.isLt)⟩

theorem columnReverseFin_involutive (N j : ℕ) (hj : 0 < j) :
    Function.Involutive (columnReverseFin N j hj) := by
  intro a
  apply Fin.ext
  change columnReverseIndex N j
    (columnReverseIndex N j (a.val % j) (a.val / j) % j)
    (columnReverseIndex N j (a.val % j) (a.val / j) / j) = a.val
  rw [columnReverseIndex_mod_eq _ _ _ _ (Nat.mod_lt _ hj),
    columnReverseIndex_div hj (Nat.mod_lt _ hj)]
  have hc : a.val % j < N := (Nat.mod_le _ _).trans_lt a.isLt
  have hrow : a.val / j < colLen N j (a.val % j) :=
    (lt_colLen_iff hj hc).mpr (by rw [Nat.mod_add_div]; exact a.isLt)
  rw [columnReverseIndex_involutive_formula _ _ _ _ (by lia), Nat.mod_add_div]

/-- The involution reversing each congruence column in the finite index set. -/
def columnReversePerm (N j : ℕ) (hj : 0 < j) : Equiv.Perm (Fin N) :=
  Function.Involutive.toPerm (columnReverseFin N j hj)
    (columnReverseFin_involutive N j hj)

theorem columnReversePerm_val (N j : ℕ) (hj : 0 < j) (a : Fin N) :
    (columnReversePerm N j hj a).val =
      columnReverseIndex N j (a.val % j) (a.val / j) := rfl

theorem columnReversePerm_at {N j c h : ℕ} (hj : 0 < j) (hc : c < j)
    (hh : c + j * h < N) :
    (columnReversePerm N j hj ⟨c + j * h, hh⟩).val =
      c + j * (colLen N j c - 1 - h) := by
  rw [columnReversePerm_val]
  simp [columnReverseIndex, Nat.add_mod, Nat.mod_eq_of_lt hc,
    Nat.add_mul_div_left _ _ hj, Nat.div_eq_of_lt hc]

end VerticalStripLLT.Circular

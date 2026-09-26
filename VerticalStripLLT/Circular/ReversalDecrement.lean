import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.ModEq

/-! The local decrement profile of the column-reversal area comparison. -/

namespace VerticalStripLLT.Circular

/-- The loss at an index under the column reversal based at `r`, with period
`j`.  It is deliberately a value-level function, so it can be used before a
finite permutation has been assembled. -/
def reversalDrop (r j a : ℕ) : ℕ :=
  if a % j = 0 then
    if r % j = 0 then
      if a = 0 then 1 else 2
    else if a = 0 then 0 else 1
  else if a % j = r % j then 1 else 0

/-- The unique multiple of `j` in the half-open interval `[r, r+j)`. -/
def reversalSourceIndex (r j : ℕ) : ℕ := j * ((r + j - 1) / j)

theorem reversalDrop_le_two (r j a : ℕ) : reversalDrop r j a ≤ 2 := by
  simp only [reversalDrop]
  split_ifs <;> simp

theorem reversalDrop_two_iff {r j a : ℕ} :
    reversalDrop r j a = 2 ↔ 0 < a ∧ a % j = 0 ∧ r % j = 0 := by
  unfold reversalDrop
  split_ifs <;> simp_all
  lia

theorem reversalDrop_add_jump_le {r j a : ℕ} (_hj : 0 < j) :
    reversalDrop r j a ≤ reversalDrop r j (a + j) := by
  simp only [reversalDrop, Nat.add_mod_right]
  split_ifs <;> simp_all

theorem reversalDrop_root_pos {r j : ℕ} (hj : 0 < j) (hjr : j < r) :
    0 < reversalDrop r j r := by
  by_cases hr : r % j = 0
  · have hrpos : 0 < r := by lia
    simp [reversalDrop, hr, Nat.ne_of_gt hrpos]
  · simp [reversalDrop, hr]

theorem reversalDrop_root_le_two (r j : ℕ) : reversalDrop r j r ≤ 2 :=
  reversalDrop_le_two r j r

theorem reversalSourceIndex_mod {r j : ℕ} (_hj : 0 < j) :
    reversalSourceIndex r j % j = 0 := by
  simp [reversalSourceIndex]

theorem reversalSourceIndex_lt_add {r j : ℕ} (hj : 0 < j) :
    reversalSourceIndex r j < r + j := by
  unfold reversalSourceIndex
  have h := Nat.div_mul_le_self (r + j - 1) j
  rw [Nat.mul_comm]
  have : j * ((r + j - 1) / j) ≤ r + j - 1 := by simpa [Nat.mul_comm] using h
  lia

theorem reversalSourceIndex_ge {r j : ℕ} (hj : 0 < j) :
    r ≤ reversalSourceIndex r j := by
  unfold reversalSourceIndex
  have hmod : (r + j - 1) % j < j := Nat.mod_lt _ hj
  have hdecomp := Nat.mod_add_div (r + j - 1) j
  lia

theorem reversalSourceIndex_mem {r j : ℕ} (hj : 0 < j) :
    r ≤ reversalSourceIndex r j ∧ reversalSourceIndex r j < r + j :=
  ⟨reversalSourceIndex_ge hj, reversalSourceIndex_lt_add hj⟩

theorem reversalSourceIndex_pos {r j : ℕ} (hj : 0 < j) (hjr : j < r) :
    0 < reversalSourceIndex r j := by
  have hr : 0 < r := by lia
  exact lt_of_lt_of_le hr (reversalSourceIndex_ge hj)

private theorem eq_of_mod_eq_of_interval {r j a b : ℕ} (hj : 0 < j)
    (hra : r ≤ a) (har : a < r + j) (hrb : r ≤ b) (hbr : b < r + j)
    (hmod : a % j = b % j) : a = b := by
  rcases le_total a b with hab | hba
  · have hcongr : a ≡ b [MOD j] := by simpa [Nat.ModEq] using hmod
    have hdvd : j ∣ b - a := (Nat.modEq_iff_dvd' hab).mp hcongr
    have hsmall : b - a < j := by lia
    have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hsmall
    lia
  · have hcongr : b ≡ a [MOD j] := by simpa [Nat.ModEq] using hmod.symm
    have hdvd : j ∣ a - b := (Nat.modEq_iff_dvd' hba).mp hcongr
    have hsmall : a - b < j := by lia
    have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hsmall
    lia

/-- A drop of two occurs only at the root among the terminal interval. -/
theorem reversalDrop_endpoint_two {r j a : ℕ} (hj : 0 < j) (_hjr : j < r)
    (hra : r ≤ a) (har : a < r + j) (hdrop : reversalDrop r j a = 2) : a = r := by
  obtain ⟨_, hmod, hrmod⟩ := reversalDrop_two_iff.mp hdrop
  exact eq_of_mod_eq_of_interval hj hra har le_rfl (by lia) (hmod.trans hrmod.symm)

/-- The only positive drops in the terminal interval occur at the root and at
the unique column source. -/
theorem reversalDrop_endpoint_pos {r j a : ℕ} (hj : 0 < j) (hjr : j < r)
    (hra : r ≤ a) (har : a < r + j) (hdrop : 0 < reversalDrop r j a) :
    a = r ∨ a = reversalSourceIndex r j := by
  have ha0 : a ≠ 0 := by
    have : 0 < r := by lia
    exact Nat.ne_of_gt (lt_of_lt_of_le this hra)
  by_cases hmod : a % j = 0
  · right
    exact eq_of_mod_eq_of_interval hj hra har (reversalSourceIndex_ge hj)
      (reversalSourceIndex_lt_add hj) (hmod.trans (reversalSourceIndex_mod hj).symm)
  · simp only [reversalDrop, ite_eq_right hmod] at hdrop
    by_cases heq : a % j = r % j
    · left
      exact eq_of_mod_eq_of_interval hj hra har le_rfl (by lia) heq
    · simp [heq] at hdrop

end VerticalStripLLT.Circular

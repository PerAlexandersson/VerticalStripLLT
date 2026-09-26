import VerticalStripLLT.Circular.ColumnIndexReversal
import VerticalStripLLT.Circular.ReversalDecrement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Integer displacement coordinates for the finite column reversal. -/

namespace VerticalStripLLT.Circular

/-- Signed displacement within the column of `a`. -/
def columnDisplacement (N j a : ℕ) : ℤ :=
  (colLen N j (a % j) : ℤ) - 1 - 2 * ((a / j : ℕ) : ℤ)

theorem columnDisplacement_def (N j a : ℕ) :
    columnDisplacement N j a =
      (colLen N j (a % j) : ℤ) - 1 - 2 * ((a / j : ℕ) : ℤ) := rfl

/-- Column lengths after adding one period.  The `r % j` initial columns get
one extra entry. -/
theorem colLen_add_period {r j c : ℕ} (hj : 0 < j) (hc : c < j) :
    colLen (r + j) j c = r / j + 1 + if c < r % j then 1 else 0 := by
  unfold colLen
  have hmod : r % j < j := Nat.mod_lt _ hj
  have hdecomp : r % j + j * (r / j) = r := Nat.mod_add_div r j
  have hsub : 1 + c ≤ r + j + j := by lia
  have hsub' : r + j + j - 1 - c + (1 + c) = r + j + j := by
    rw [Nat.sub_sub]
    exact Nat.sub_add_cancel hsub
  by_cases hcs : c < r % j
  · rw [ite_eq_left hcs]
    apply Nat.div_eq_of_lt_le <;> nlinarith [Nat.zero_le (r % j)]
  · rw [ite_eq_right hcs]
    apply Nat.div_eq_of_lt_le <;> nlinarith [Nat.zero_le (r % j)]

/-- Away from a column boundary, taking a predecessor only lowers the
remainder and leaves the quotient unchanged. -/
theorem pred_mod_of_mod_pos {a j : ℕ} (hj : 0 < j) (ha : 0 < a % j) :
    (a - 1) % j = a % j - 1 := by
  have hdecomp : a % j + j * (a / j) = a := Nat.mod_add_div a j
  have hrewrite : a - 1 = (a % j - 1) + j * (a / j) := by lia
  have hsmall : a % j - 1 < j := by have := Nat.mod_lt a hj; lia
  rw [hrewrite]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hsmall]


theorem pred_div_of_mod_pos {a j : ℕ} (hj : 0 < j) (ha : 0 < a % j) :
    (a - 1) / j = a / j := by
  have hdecomp : a % j + j * (a / j) = a := Nat.mod_add_div a j
  have hrewrite : a - 1 = (a % j - 1) + j * (a / j) := by lia
  rw [hrewrite, Nat.add_mul_div_left _ _ hj,
    Nat.div_eq_of_lt (show a % j - 1 < j by have := Nat.mod_lt a hj; lia)]
  simp

/-- At a column boundary, the predecessor wraps to the final residue and
lowers the quotient by one. -/
theorem pred_mod_of_mod_zero {a j : ℕ} (hj : 0 < j) (ha : 0 < a)
    (hmod : a % j = 0) :
    (a - 1) % j = j - 1 := by
  have hdecomp : a % j + j * (a / j) = a := Nat.mod_add_div a j
  have hq : 0 < a / j := by
    by_contra hq
    have : a / j = 0 := by lia
    rw [hmod, this] at hdecomp
    simp at hdecomp
    lia
  have hrewrite : a - 1 = (j - 1) + j * (a / j - 1) := by
    rw [hmod] at hdecomp
    have hq1 := Nat.sub_add_cancel hq
    have hj1 := Nat.sub_add_cancel hj
    have ha1 := Nat.sub_add_cancel ha
    nlinarith
  rw [hrewrite, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (Nat.sub_lt hj Nat.zero_lt_one)]
  simp

theorem pred_div_of_mod_zero {a j : ℕ} (hj : 0 < j) (ha : 0 < a)
    (hmod : a % j = 0) :
    (a - 1) / j = a / j - 1 := by
  have hdecomp : a % j + j * (a / j) = a := Nat.mod_add_div a j
  have hq : 0 < a / j := by
    by_contra hq
    have : a / j = 0 := by lia
    rw [hmod, this] at hdecomp
    simp at hdecomp
    lia
  have hrewrite : a - 1 = (j - 1) + j * (a / j - 1) := by
    rw [hmod] at hdecomp
    have hq1 := Nat.sub_add_cancel hq
    have hj1 := Nat.sub_add_cancel hj
    have ha1 := Nat.sub_add_cancel ha
    nlinarith
  rw [hrewrite, Nat.add_mul_div_left _ _ hj, Nat.div_eq_of_lt (Nat.sub_lt hj Nat.zero_lt_one)]
  simp

/-- Consecutive chain vertices have displacements differing by the target drop. -/
theorem columnDisplacement_pred {r j a : ℕ} (hj : 0 < j) (ha : 0 < a) :
    columnDisplacement (r + j) j (a - 1) - columnDisplacement (r + j) j a =
      if a % j = 0 then (if r % j = 0 then 2 else 1)
      else (if a % j = r % j then 1 else 0) := by
  have hrmod := Nat.mod_lt r hj
  have hamod := Nat.mod_lt a hj
  by_cases hm : a % j = 0
  · have hq : 0 < a / j := by
      have hd := Nat.mod_add_div a j
      by_contra hq
      have hz : a / j = 0 := by lia
      simp [hm, hz] at hd
      lia
    unfold columnDisplacement
    rw [pred_mod_of_mod_zero hj ha hm, pred_div_of_mod_zero hj ha hm, hm,
      colLen_add_period hj (show j - 1 < j by lia), colLen_add_period hj hj,
      Int.ofNat_sub hq]
    have hn : ¬ j - 1 < r % j := by lia
    by_cases hr : r % j = 0
    · simp [hr]
      ring
    · have hrp : 0 < r % j := by lia
      simp [hn, hr, hrp]
      ring
  · have hmp : 0 < a % j := by lia
    unfold columnDisplacement
    rw [pred_mod_of_mod_pos hj hmp, pred_div_of_mod_pos hj hmp,
      colLen_add_period hj (show a % j - 1 < j by lia), colLen_add_period hj hamod]
    simp only [ite_eq_right hm]
    split_ifs <;> push_cast <;> lia

/-- The source exception in the decrement is exactly one extra unit. -/
theorem columnDisplacement_pred_eq_drop {r j a b : ℕ} (hj : 0 < j) (ha : 0 < a)
    (hb : b % j = a % j) :
    columnDisplacement (r + j) j (a - 1) - columnDisplacement (r + j) j a =
      (reversalDrop r j b : ℤ) + (if b = 0 then 1 else 0) := by
  rw [columnDisplacement_pred hj ha]
  unfold reversalDrop
  rw [hb]
  by_cases hb0 : b = 0
  · subst b
    simp only [Nat.zero_mod] at hb
    simp [← hb]
    split_ifs <;> norm_num
  · simp only [ite_eq_right hb0]
    split_ifs <;> norm_num

end VerticalStripLLT.Circular

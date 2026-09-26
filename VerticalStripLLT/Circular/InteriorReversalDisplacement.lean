import VerticalStripLLT.Circular.InteriorReversalTarget
import VerticalStripLLT.Circular.ColumnDisplacement

/-! Exact area changes along the reversed strict component. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- A single source correction makes the old area constant on each index column. -/
theorem area_vertex_column (a : Fin (r + j)) :
    D.area.area (K.vertex a.val) + (if a.val = 0 then 1 else 0) =
      D.area.area (K.vertex (a.val % j)) + (if a.val % j = 0 then 1 else 0) := by
  have hj : 0 < j := by have := K.two_le; lia
  have hdecomp := Nat.mod_add_div a.val j
  by_cases ha : a.val = 0
  · simp [ha]
  by_cases hc : a.val % j = 0
  · have hq : 0 < a.val / j := by
      by_contra hq
      have hq0 : a.val / j = 0 := by lia
      simp [hc, hq0] at hdecomp
      exact ha hdecomp.symm
    have hform : a.val = j * (a.val / j - 1 + 1) := by
      rw [Nat.sub_add_cancel hq]
      simpa [hc] using hdecomp.symm
    have hp := K.area_zero_column_succ (a.val / j - 1) (by rw [← hform]; exact a.isLt)
    rw [← hform] at hp
    simp [ha, hc, hp]
  · have hp := K.area_at_column_index (a.val % j) (a.val / j) (by lia)
      (by rw [hdecomp]; exact a.isLt)
    rw [hdecomp] at hp
    simp [ha, hc, hp]

/-- Reversing an old strict head changes its old height only at the old source. -/
theorem area_reversed_vertex (a : Fin (r + j)) (ha : 0 < a.val) :
    D.area.area (K.vertex (columnReverseIndex (r + j) j (a.val % j) (a.val / j))) +
        (if columnReverseIndex (r + j) j (a.val % j) (a.val / j) = 0 then 1 else 0) =
      D.area.area (K.vertex a.val) := by
  have hj : 0 < j := by have := K.two_le; lia
  let b := columnReverseFin (r + j) j hj a
  have hp := K.area_vertex_column b
  have hmod : b.val % j = a.val % j :=
    columnReverseIndex_mod_eq _ _ _ _ (Nat.mod_lt _ hj)
  rw [hmod, ← K.area_vertex_column a, ite_eq_right (by lia : a.val ≠ 0), Nat.add_zero] at hp
  exact hp

/-- Integer subtraction agrees with the actual natural-valued target area. -/
theorem reversalArea_vertex_int (a : Fin (r + j)) :
    (K.reversalArea.area (K.vertex a.val) : ℤ) =
      (D.area.area (K.vertex a.val) : ℤ) - (reversalDrop r j a.val : ℤ) := by
  have hp := K.reversalArea_vertex_pos a
  change 0 < D.area.area (K.vertex a.val) - K.reversalDecrement (K.vertex a.val) at hp
  rw [K.reversalDecrement_vertex a] at hp
  change ((D.area.area (K.vertex a.val) - K.reversalDecrement (K.vertex a.val) : ℕ) : ℤ) = _
  rw [K.reversalDecrement_vertex a, Int.ofNat_sub (by lia)]

/-- A reversed strict edge has its original length plus the endpoint displacements. -/
theorem reversalArea_reversed_length (a : Fin (r + j)) (ha : 0 < a.val) :
    (K.reversalArea.area (K.reversalPerm (K.vertex a.val)) : ℤ) =
      (D.area.area (K.vertex a.val) : ℤ) + columnDisplacement (r + j) j a.val -
        columnDisplacement (r + j) j (a.val - 1) := by
  have hj : 0 < j := by have := K.two_le; lia
  let b := columnReverseFin (r + j) j hj a
  have harea := K.area_reversed_vertex a ha
  change D.area.area (K.vertex b.val) + (if b.val = 0 then 1 else 0) =
    D.area.area (K.vertex a.val) at harea
  have hdrop := columnDisplacement_pred_eq_drop (r := r) hj ha
    (columnReverseIndex_mod_eq (r + j) j (a.val % j) (a.val / j) (Nat.mod_lt _ hj))
  change columnDisplacement (r + j) j (a.val - 1) - columnDisplacement (r + j) j a.val =
    (reversalDrop r j b.val : ℤ) + (if b.val = 0 then 1 else 0) at hdrop
  rw [K.reversalPerm_vertex a]
  change (K.reversalArea.area (K.vertex b.val) : ℤ) = _
  rw [K.reversalArea_vertex_int b]
  by_cases hb : b.val = 0
  · simp only [ite_eq_left hb] at harea hdrop
    exact_mod_cast (show (D.area.area (K.vertex b.val) : ℤ) - reversalDrop r j b.val =
      (D.area.area (K.vertex a.val) : ℤ) + columnDisplacement (r + j) j a.val -
        columnDisplacement (r + j) j (a.val - 1) by lia)
  · simp only [ite_eq_right hb, add_zero] at harea hdrop
    rw [harea]
    lia

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

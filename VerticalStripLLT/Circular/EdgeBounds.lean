import VerticalStripLLT.Circular.Diagram

/-! Elementary bounds and modular endpoint facts for circular edges. -/

namespace VerticalStripLLT.Circular

namespace Edge

variable {n : ℕ} {A : CircularArea n} (e : Edge A)

theorem length_pos : 0 < e.length.val := e.2.1

theorem length_lt_n : e.length.val < n := e.length.isLt

theorem length_le_area : e.length.val ≤ A.area e.head := e.2.2

theorem tail_add_length_mod :
    (e.tail.val + e.length.val) % n = e.head.val := by
  have hle : e.length.val ≤ e.head.val + n := by
    have := e.length_lt_n
    lia
  calc
    (e.tail.val + e.length.val) % n =
        (((e.head.val + n - e.length.val) % n) + e.length.val) % n := by
          rfl
    _ = (e.head.val + n - e.length.val + e.length.val) % n := by
      rw [Nat.add_mod]
      simp
    _ = (e.head.val + n) % n := by rw [Nat.sub_add_cancel hle]
    _ = e.head.val := by
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt e.head.isLt

theorem tail_ne_head : e.tail ≠ e.head := by
  have hpos := e.length_pos
  have hlt := e.length_lt_n
  have hhead := e.head.isLt
  intro h
  have hv : e.tail.val = e.head.val := congrArg Fin.val h
  by_cases hle : e.length.val ≤ e.head.val
  · have hsub : e.head.val + n - e.length.val =
        (e.head.val - e.length.val) + n := by
      lia
    have htail : e.tail.val = e.head.val - e.length.val := by
      change (e.head.val + n - e.length.val) % n = _
      rw [hsub, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by lia)
    lia
  · have hsub : e.head.val + n - e.length.val =
        e.head.val + (n - e.length.val) := by
      rw [Nat.add_sub_assoc]
      exact le_of_lt e.length_lt_n
    have htail : e.tail.val = e.head.val + (n - e.length.val) := by
      change (e.head.val + n - e.length.val) % n = _
      rw [hsub]
      apply Nat.mod_eq_of_lt
      lia
    lia

end Edge
end VerticalStripLLT.Circular

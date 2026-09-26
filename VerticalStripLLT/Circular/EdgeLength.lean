import VerticalStripLLT.Circular.EdgeBounds
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-! Length comparisons for edges with prescribed circular endpoints. -/

namespace VerticalStripLLT.Circular
namespace Edge

variable {n : ℕ} {A B : CircularArea n}

private theorem length_eq_of_tail_mod {x y t : ℕ} (_hn : 0 < n)
    (hx : x < n) (hy : y < n)
    (h : t + x ≡ t + y [MOD n]) : x = y := by
  have h' := Nat.ModEq.add_left_cancel' t h
  exact h'.eq_of_lt_of_lt hx hy

private theorem succ_eq_of_mod_eq {x y : ℕ} (_hn : 0 < n)
    (hx : x < n) (hypos : 0 < y) (_hy : y < n)
    (h : (x + 1) % n = y) : x + 1 = y := by
  have hle : x + 1 ≤ n := by lia
  by_cases hlt : x + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact h
  · have hxn : x + 1 = n := by lia
    have hyzero : y = 0 := by simpa [hxn] using h.symm
    lia

private theorem endpoint_mod {e : Edge A} :
    e.tail.val + e.length.val ≡ e.head.val [MOD n] := by
  change (e.tail.val + e.length.val) % n = e.head.val % n
  rw [e.tail_add_length_mod, Nat.mod_eq_of_lt e.head.isLt]

private theorem next_val_mod {i : Fin n} :
    (A.next i).val ≡ i.val + 1 [MOD n] := by
  change ((i.val + 1) % n) % n = (i.val + 1) % n
  rw [Nat.mod_mod]

theorem length_eq_of_endpoints {e : Edge A} {f : Edge B}
    (ht : f.tail = e.tail) (hh : f.head = e.head) :
    f.length.val = e.length.val := by
  have he := endpoint_mod (e := e)
  have hf := endpoint_mod (e := f)
  have hmod : e.tail.val + f.length.val ≡
      e.tail.val + e.length.val [MOD n] := by
    calc
      e.tail.val + f.length.val ≡ f.tail.val + f.length.val [MOD n] := by
        rw [congrArg Fin.val ht]
      _ ≡ f.head.val [MOD n] := hf
      _ = e.head.val := congrArg Fin.val hh
      _ ≡ e.tail.val + e.length.val [MOD n] := he.symm
  exact length_eq_of_tail_mod A.positive f.length_lt_n e.length_lt_n hmod

theorem length_eq_of_next_both {e : Edge A} {f : Edge B}
    (ht : f.tail = A.next e.tail) (hh : f.head = A.next e.head) :
    f.length.val = e.length.val := by
  have he := endpoint_mod (e := e)
  have hf := endpoint_mod (e := f)
  have htail : f.tail.val ≡ e.tail.val + 1 [MOD n] := by
    calc
      f.tail.val ≡ (A.next e.tail).val [MOD n] := by
        rw [congrArg Fin.val ht]
      _ ≡ e.tail.val + 1 [MOD n] := next_val_mod
  have hhead : f.head.val ≡ e.head.val + 1 [MOD n] := by
    calc
      f.head.val ≡ (A.next e.head).val [MOD n] := by
        rw [congrArg Fin.val hh]
      _ ≡ e.head.val + 1 [MOD n] := next_val_mod
  have hmiddle : (e.tail.val + 1) + f.length.val ≡
      e.head.val + 1 [MOD n] := by
    calc
      (e.tail.val + 1) + f.length.val ≡
          f.tail.val + f.length.val [MOD n] := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.ModEq.add_right f.length.val htail.symm
      _ ≡ f.head.val [MOD n] := hf
      _ ≡ e.head.val + 1 [MOD n] := hhead
  have hmiddle' : 1 + (e.tail.val + f.length.val) ≡
      1 + e.head.val [MOD n] := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmiddle
  have hcancel := Nat.ModEq.add_left_cancel' 1 hmiddle'
  have hmod : e.tail.val + f.length.val ≡
      e.tail.val + e.length.val [MOD n] := by
    calc
      e.tail.val + f.length.val ≡ e.head.val [MOD n] := hcancel
      _ ≡ e.tail.val + e.length.val [MOD n] := he.symm
  exact length_eq_of_tail_mod A.positive f.length_lt_n e.length_lt_n hmod

theorem length_succ_of_next_head {e : Edge A} {f : Edge B}
    (ht : f.tail = e.tail) (hh : f.head = A.next e.head) :
    f.length.val = e.length.val + 1 := by
  have he := endpoint_mod (e := e)
  have hf := endpoint_mod (e := f)
  have hhead : f.head.val ≡ e.head.val + 1 [MOD n] := by
    calc
      f.head.val ≡ (A.next e.head).val [MOD n] := by
        rw [congrArg Fin.val hh]
      _ ≡ e.head.val + 1 [MOD n] := next_val_mod
  have hmod : e.tail.val + f.length.val ≡
      e.tail.val + (e.length.val + 1) [MOD n] := by
    calc
      e.tail.val + f.length.val ≡ f.tail.val + f.length.val [MOD n] := by
        rw [congrArg Fin.val ht]
      _ ≡ f.head.val [MOD n] := hf
      _ ≡ e.head.val + 1 [MOD n] := hhead
      _ ≡ e.tail.val + (e.length.val + 1) [MOD n] := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.ModEq.add_right 1 he.symm
  have hmod' := Nat.ModEq.add_left_cancel' e.tail.val hmod
  have hraw : (e.length.val + 1) % n = f.length.val := by
    exact Eq.trans (Eq.symm hmod') (Nat.mod_eq_of_lt f.length_lt_n)
  exact (succ_eq_of_mod_eq A.positive e.length.isLt f.length_pos
    f.length_lt_n hraw).symm

theorem length_succ_of_next_tail {e : Edge A} {f : Edge B}
    (ht : f.tail = A.next e.tail) (hh : f.head = e.head) :
    f.length.val + 1 = e.length.val := by
  have he := endpoint_mod (e := e)
  have hf := endpoint_mod (e := f)
  have htail : f.tail.val ≡ e.tail.val + 1 [MOD n] := by
    calc
      f.tail.val ≡ (A.next e.tail).val [MOD n] := by
        rw [congrArg Fin.val ht]
      _ ≡ e.tail.val + 1 [MOD n] := next_val_mod
  have hmod : e.tail.val + (f.length.val + 1) ≡
      e.tail.val + e.length.val [MOD n] := by
    calc
      e.tail.val + (f.length.val + 1) ≡
          f.tail.val + f.length.val [MOD n] := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.ModEq.add_right f.length.val htail.symm
      _ ≡ f.head.val [MOD n] := hf
      _ = e.head.val := congrArg Fin.val hh
      _ ≡ e.tail.val + e.length.val [MOD n] := he.symm
  have hmod' := Nat.ModEq.add_left_cancel' e.tail.val hmod
  have hraw : (f.length.val + 1) % n = e.length.val := by
    exact Eq.trans hmod' (Nat.mod_eq_of_lt e.length_lt_n)
  exact succ_eq_of_mod_eq A.positive f.length.isLt e.length_pos
    e.length_lt_n hraw

end Edge
end VerticalStripLLT.Circular

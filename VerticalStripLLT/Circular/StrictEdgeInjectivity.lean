import VerticalStripLLT.Circular.CutOrder
import VerticalStripLLT.Circular.EdgeBounds

/-! Injectivity properties of strict circular edges. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} {D : Diagram n}

private theorem atOffset_add (A : CircularArea n) (c : Fin n) (a b : ℕ) :
    A.atOffset (A.atOffset c a) b = A.atOffset c (a + b) := by
  apply Fin.ext
  simp [CircularArea.atOffset, Nat.add_assoc]

private theorem next_eq_atOffset_one (A : CircularArea n) (c : Fin n) :
    A.next c = A.atOffset c 1 := by
  apply Fin.ext
  simp [CircularArea.atOffset, CircularArea.next]

private theorem head_offset_of_same_tail {e f : Edge D.area}
    (ht : e.tail = f.tail) (hLM : e.length.val ≤ f.length.val) :
    f.head = D.area.atOffset e.head (f.length.val - e.length.val) := by
  apply Fin.ext
  change f.head.val = (e.head.val + (f.length.val - e.length.val)) % n
  symm
  rw [← e.tail_add_length_mod, ← f.tail_add_length_mod, ← ht]
  simp only [Nat.mod_add_mod]
  congr 1
  lia

private theorem no_strict_tail_length_lt {e f : Edge D.area}
    (he : e ∈ D.strict) (ht : e.tail = f.tail)
    (hLM : e.length.val < f.length.val) : False := by
  have hhead := head_offset_of_same_tail ht (le_of_lt hLM)
  let d := f.length.val - e.length.val
  have hdpos : 0 < d := by
    dsimp only [d]
    lia
  have hnext : D.area.atOffset (D.area.next e.head) (d - 1) = f.head := by
    rw [next_eq_atOffset_one, atOffset_add, hhead]
    dsimp only [d]
    congr 1
    lia
  have harea := D.area.area_atOffset_le (D.area.next e.head) (d - 1)
  rw [hnext] at harea
  have hce := D.strict_corner e he
  have hnextle : D.area.area (D.area.next e.head) ≤ e.length.val := by
    exact hce.2.trans_eq hce.1.symm
  have hbound : D.area.area f.head ≤ f.length.val - 1 := by
    dsimp only [d] at harea ⊢
    lia
  have hflen := f.length_le_area
  lia

theorem strict_edge_eq_of_head_eq {e f : Edge D.area}
    (he : e ∈ D.strict) (hf : f ∈ D.strict) (hh : e.head = f.head) : e = f := by
  have hce := D.strict_corner e he
  have hcf := D.strict_corner f hf
  apply Subtype.ext
  apply Prod.ext
  · exact hh
  · apply Fin.ext
    change e.length.val = f.length.val
    rw [hce.1, hcf.1, hh]

theorem strict_edge_eq_of_tail_eq {e f : Edge D.area}
    (he : e ∈ D.strict) (hf : f ∈ D.strict) (ht : e.tail = f.tail) : e = f := by
  by_cases hlen : e.length.val = f.length.val
  · apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hhead := e.tail_add_length_mod
      have hhead' := f.tail_add_length_mod
      rw [hlen, ht] at hhead
      exact hhead.symm.trans hhead'
    · apply Fin.ext
      exact hlen
  · rcases lt_or_gt_of_ne hlen with hlt | hlt
    · exact False.elim (no_strict_tail_length_lt he ht hlt)
    · exact False.elim (no_strict_tail_length_lt hf ht.symm hlt)

end Diagram
end VerticalStripLLT.Circular

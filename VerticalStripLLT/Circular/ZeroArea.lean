import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Circular.EdgeBounds

/-! Structural facts for diagrams with no non-strict edges. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} {D : Diagram n}

private theorem strict_of_no_normal (h : D.edgeData.normalEdges = ∅)
    (e : Edge D.area) : e ∈ D.strict := by
  by_contra he
  have hn : e ∈ D.edgeData.normalEdges := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩
  rw [h] at hn
  exact Finset.notMem_empty _ hn

theorem area_le_one_of_no_normal (h : D.edgeData.normalEdges = ∅) (i : Fin n) :
    D.area.area i ≤ 1 := by
  by_cases hi : 0 < D.area.area i
  · have hn : 1 < n := lt_of_le_of_lt hi (D.area.bound i)
    let e : Edge D.area :=
      ⟨(i, ⟨1, hn⟩), by
        exact ⟨Nat.zero_lt_one, hi⟩⟩
    have hc := D.strict_corner e (strict_of_no_normal h e)
    have heq : 1 = D.area.area i := by
      exact hc.1
    exact heq.ge
  · have hi0 : D.area.area i = 0 := Nat.eq_zero_of_not_pos hi
    simp [hi0]

theorem edge_length_eq_one_of_no_normal (h : D.edgeData.normalEdges = ∅)
    (e : Edge D.area) : e.length.val = 1 := by
  have harea : D.area.area e.head ≤ 1 := area_le_one_of_no_normal h e.head
  exact Nat.le_antisymm (e.length_le_area.trans harea) e.length_pos

theorem edge_eq_of_head_eq_of_no_normal (h : D.edgeData.normalEdges = ∅)
    {e f : Edge D.area} (hh : e.head = f.head) : e = f := by
  apply Subtype.ext
  apply Prod.ext
  · exact hh
  · apply Fin.ext
    change e.length.val = f.length.val
    rw [edge_length_eq_one_of_no_normal h e,
      edge_length_eq_one_of_no_normal h f]

theorem edge_eq_of_tail_eq_of_no_normal (h : D.edgeData.normalEdges = ∅)
    {e f : Edge D.area} (ht : e.tail = f.tail) : e = f := by
  apply edge_eq_of_head_eq_of_no_normal h
  apply Fin.ext
  have he := e.tail_add_length_mod
  have hf := f.tail_add_length_mod
  rw [edge_length_eq_one_of_no_normal h e, ht] at he
  rw [edge_length_eq_one_of_no_normal h f] at hf
  exact he.symm.trans hf

end Diagram
end VerticalStripLLT.Circular

import VerticalStripLLT.Circular.ZeroArea

/-! Strict incoming edges and zero-area witnesses. -/

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

theorem strict_incoming_iff_area_pos_of_no_normal
    (hN : D.edgeData.normalEdges = ∅) (i : Fin n) :
    (∃ e ∈ D.strict, e.head = i) ↔ 0 < D.area.area i := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact lt_of_lt_of_le e.length_pos e.length_le_area
  · intro hi
    have hn : 1 < n := lt_of_le_of_lt hi (D.area.bound i)
    let e : Edge D.area :=
      ⟨(i, ⟨1, hn⟩), by exact ⟨Nat.zero_lt_one, hi⟩⟩
    exact ⟨e, strict_of_no_normal hN e, rfl⟩

theorem exists_zero_head_of_not_strict_incoming
    (hN : D.edgeData.normalEdges = ∅)
    (h : ¬∀ i, ∃ e ∈ D.strict, e.head = i) :
    ∃ i, D.area.area i = 0 := by
  classical
  by_contra hzero
  apply h
  intro i
  apply (strict_incoming_iff_area_pos_of_no_normal hN i).mpr
  by_contra hi
  apply hzero
  exact ⟨i, Nat.eq_zero_of_not_pos hi⟩

theorem strict_incoming_of_all_positive
    (hN : D.edgeData.normalEdges = ∅)
    (hpos : ∀ i, 0 < D.area.area i) :
    ∀ i, ∃ e ∈ D.strict, e.head = i := by
  intro i
  exact (strict_incoming_iff_area_pos_of_no_normal hN i).mpr (hpos i)

theorem no_edge_with_zero_head_area (i : Fin n)
    (hi : D.area.area i = 0) :
    ∀ e : Edge D.area, e.head ≠ i := by
  intro e heq
  have hle := e.length_le_area
  rw [heq, hi] at hle
  exact (Nat.not_lt_zero _ (lt_of_lt_of_le e.length_pos hle))

end Diagram
end VerticalStripLLT.Circular

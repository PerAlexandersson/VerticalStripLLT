import VerticalStripLLT.Circular.InteriorLiftIntervals

/-! The exceptional nonstrict source row under column reversal. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

/-- The old source's boundary starts at the first vertex of the preceding column. -/
theorem residue_boundary_source (z : ℤ) (hz : D.residue z = K.vertex 0) :
    D.residue (D.boundary z) = K.vertex (j - 1) := by
  have hj := K.two_le
  have hjr := K.jump_lt
  have hh : D.residue (z + 1) = K.vertex j := by
    rw [D.residue_succ, hz, K.next_jump 0 (by lia), Nat.zero_add]
  have hb : D.boundary (z + 1) = D.boundary z := by
    rw [boundary, boundary, hh, hz, K.source_area_jump]
    push_cast
    ring
  obtain ⟨e, he, ht, heh⟩ := K.exists_strict_edge j (by lia) (by lia)
  have hs := D.selected_of_strictAt (show D.strictAt (z + 1) from ⟨e, he, heh.trans hh.symm⟩)
  rw [hb, hh, K.selected_to_vertex_iff (show j < r + j by lia)] at hs
  exact hs.2

/-- The new source threshold lies just after the last column's lifted interval. -/
theorem boundary_reversalLift_source (z : ℤ) (hz : D.residue z = K.vertex 0) :
    K.reversalTarget.boundary (K.reversalLift z) =
      D.boundary z + (colLen (r + j) j (j - 1) : ℤ) := by
  have hj : 0 < j := by have := K.two_le; lia
  let a : Fin (r + j) := ⟨reversalSourceIndex r j, reversalSourceIndex_lt_add hj⟩
  have hap : 0 < a.val := reversalSourceIndex_pos hj K.jump_lt
  have hamod : a.val % j = 0 := reversalSourceIndex_mod hj
  have hprofile := K.area_vertex_column a
  simp only [ite_eq_right (by lia : a.val ≠ 0), Nat.add_zero, hamod]
    at hprofile
  have hshift : K.reversalLift z = z + (colLen (r + j) j 0 : ℤ) - 1 := by
    change z + K.reversalShift (D.residue z) = _
    rw [hz, K.reversalShift_vertex ⟨0, by have := K.two_le; lia⟩]
    simp [columnDisplacement]
    ring
  rw [boundary, K.reversalLift_residue, hz, K.reversalPerm_vertex_zero, hshift]
  change z + (colLen (r + j) j 0 : ℤ) - 1 -
    (K.reversalArea.area (K.vertex a.val) : ℤ) = _
  rw [K.reversalArea_vertex_int a, boundary, hz,
    colLen_add_period hj hj, colLen_add_period hj (show j - 1 < j by lia)]
  have hrmod := Nat.mod_lt r hj
  have hn : ¬ j - 1 < r % j := by lia
  by_cases hr : r % j = 0
  · simp only [hr, Nat.lt_irrefl]
    have hd : reversalDrop r j a.val = 2 := by
      simp [reversalDrop, hamod, hr, show a.val ≠ 0 by lia]
    rw [hd]
    push_cast
    lia
  · have hrp : 0 < r % j := by lia
    simp only [ite_eq_left hrp, ite_eq_right hn]
    have hd : reversalDrop r j a.val = 1 := by
      simp [reversalDrop, hamod, hr, show a.val ≠ 0 by lia]
    rw [hd]
    push_cast
    lia

/-- Moving the source threshold across its last column crosses no exterior point. -/
theorem boundary_source_le_outside_iff (z x : ℤ)
    (hz : D.residue z = K.vertex 0) (hx : D.residue x ∉ K.componentVertices) :
    K.reversalTarget.boundary (K.reversalLift z) ≤ x ↔ D.boundary z ≤ x := by
  have hj : 0 < j := by have := K.two_le; lia
  have hjr := K.jump_lt
  let a : Fin (r + j) := ⟨j - 1, by lia⟩
  have hamod : a.val % j = j - 1 := Nat.mod_eq_of_lt (by lia)
  have hadiv : a.val / j = 0 := Nat.div_eq_of_lt (by lia)
  have hres : D.residue (D.boundary z) = K.vertex a.val := K.residue_boundary_source z hz
  have hnot : ¬ (D.boundary z ≤ x ∧ x ≤ D.boundary z +
      (colLen (r + j) j (j - 1) : ℤ) - 1) := by
    rintro ⟨hl, hu⟩
    apply hx
    apply K.residue_mem_column_interval a (D.boundary z) hres x
    · simpa only [hadiv, Nat.cast_zero, sub_zero] using hl
    · simpa only [hamod, hadiv, Nat.cast_zero, sub_zero] using hu
  rw [K.boundary_reversalLift_source z hz]
  have hlen : 0 ≤ (colLen (r + j) j (j - 1) : ℤ) := Int.natCast_nonneg _
  lia

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

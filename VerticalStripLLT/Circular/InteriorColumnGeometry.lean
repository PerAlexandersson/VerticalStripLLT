import VerticalStripLLT.Circular.InteriorMergedComponent
import VerticalStripLLT.Circular.CutOrder
import VerticalStripLLT.Circular.EdgeLength

/-! Consecutive circular columns and their original area profiles. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- Every residue column of the chain index is a consecutive circular interval. -/
theorem vertex_atOffset (c h : ℕ) (hc : c < j) (hh : c + j * h < r + j) :
    K.vertex (c + j * h) = D.area.atOffset (K.vertex c) h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc] at hh ⊢
    have hp : c + j * h < r := by lia
    rw [← K.next_jump _ hp, ih (by lia), D.area.atOffset_succ]

/-- The strict edge entering a positive chain index has the preceding chain vertex as tail. -/
theorem exists_strict_edge (a : ℕ) (ha : 0 < a) (ha' : a < r + j) :
    ∃ e ∈ D.strict, e.tail = K.vertex (a - 1) ∧ e.head = K.vertex a := by
  have hs := K.step (a - 1) (by lia)
  rw [Nat.sub_add_cancel ha] at hs
  obtain ⟨e, he, ht, hh⟩ := hs
  exact ⟨e, by simpa [Diagram.edgeData] using he, ht, hh⟩

/-- Area is unchanged by a contact jump away from the nonstrict source. -/
theorem area_jump (a : ℕ) (ha : 0 < a) (ha' : a < r) :
    D.area.area (K.vertex (a + j)) = D.area.area (K.vertex a) := by
  have hj := K.two_le
  obtain ⟨e, he, het, heh⟩ := K.exists_strict_edge a ha (by lia)
  obtain ⟨f, hf, hft, hfh⟩ := K.exists_strict_edge (a + j) (by lia) (by lia)
  have ht : f.tail = D.area.next e.tail := by
    rw [hft, het, K.next_jump (a - 1) (by lia)]
    congr 1
    lia
  have hh : f.head = D.area.next e.head := by
    rw [hfh, heh, K.next_jump a ha']
  have hlen := Edge.length_eq_of_next_both ht hh
  rw [(D.strict_corner f hf).1, (D.strict_corner e he).1, hfh, heh] at hlen
  exact hlen

/-- The initial nonstrict row is one cell shorter than its successor in column zero. -/
theorem source_area_jump :
    D.area.area (K.vertex j) = D.area.area (K.vertex 0) + 1 := by
  let z := D.boundary^[r] t
  have hn : ¬ D.strictAt z := by
    intro hs
    have he := D.selected_of_strictAt hs
    rw [← K.source] at he
    exact K.source_free _ he
  have hg := K.source_gap
  change D.eastGap z = 0 at hg
  rw [Diagram.eastGap, ite_eq_right hn, Diagram.boundary, Diagram.boundary] at hg
  have hv : D.residue (z + 1) = K.vertex j := by
    rw [D.residue_succ, ← K.source, K.next_jump 0 (by have := K.jump_lt; lia)]
    simp
  rw [hv, ← K.source] at hg
  exact_mod_cast (show (D.area.area (K.vertex j) : ℤ) =
    (D.area.area (K.vertex 0) : ℤ) + 1 by lia)

/-- All successive vertices of a column beginning at a positive chain index have equal area. -/
theorem area_at_column_index (c h : ℕ) (hc : 0 < c) (hh : c + j * h < r + j) :
    D.area.area (K.vertex (c + j * h)) = D.area.area (K.vertex c) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc] at hh ⊢
    rw [K.area_jump (c + j * h) (by lia) (by lia)]
    exact ih (by lia)

private theorem next_tail_eq_head {e : Edge D.area} (he : e.length.val = 1) :
    D.area.next e.tail = e.head := by
  apply Fin.ext
  have hh := e.tail_add_length_mod
  change (e.tail.val + 1) % n = e.head.val
  simpa only [he] using hh

private theorem next_next_tail_eq_head {e : Edge D.area} (he : e.length.val = 2) :
    D.area.next (D.area.next e.tail) = e.head := by
  apply Fin.ext
  have hh := e.tail_add_length_mod
  change ((e.tail.val + 1) % n + 1) % n = e.head.val
  rw [Nat.mod_add_mod]
  simpa only [he, Nat.add_assoc, Nat.reduceAdd] using hh

/-- Distinct adjacent columns rule out a length-one incoming strict edge. -/
theorem area_ge_two_of_positive_main (a : ℕ) (ha : 0 < a) (ha' : a ≤ r) :
    2 ≤ D.area.area (K.vertex a) := by
  have hj := K.two_le
  obtain ⟨e, he, het, heh⟩ := K.exists_strict_edge a ha (by lia)
  have harea := (D.strict_corner e he).1
  rw [heh] at harea
  by_contra hsmall
  have hlen : e.length.val = 1 := by have := e.length_pos; lia
  have hnext := next_tail_eq_head hlen
  rw [het, heh, K.next_jump (a - 1) (by lia)] at hnext
  have := K.injective (by lia) (by lia) hnext
  lia

/-- The source row contains at least two cells, so its planned one-cell decrease stays positive. -/
theorem source_area_ge_two : 2 ≤ D.area.area (K.vertex 0) := by
  have hj := K.two_le
  have hjr := K.jump_lt
  obtain ⟨e, he, het, heh⟩ := K.exists_strict_edge j (by lia) (by lia)
  have harea := (D.strict_corner e he).1
  rw [heh, K.source_area_jump] at harea
  have hlen2 : 2 ≤ e.length.val := by
    have h := K.area_ge_two_of_positive_main j (by lia) (by lia)
    rw [← heh, ← (D.strict_corner e he).1] at h
    exact h
  by_contra hsmall
  have hlen : e.length.val = 2 := by lia
  have hnext := next_next_tail_eq_head hlen
  have hzero := K.next_jump 0 (by lia)
  simp only [Nat.zero_add] at hzero
  rw [het, heh, ← hzero] at hnext
  have heq := D.area.next_injective hnext
  rw [K.next_jump (j - 1) (by lia)] at heq
  have := K.injective (by lia) (by lia) heq
  lia

/-- The positive rows of column zero are exactly one cell longer than its source. -/
theorem area_zero_column_succ (h : ℕ) (hh : j * (h + 1) < r + j) :
    D.area.area (K.vertex (j * (h + 1))) = D.area.area (K.vertex 0) + 1 := by
  have heq : j * (h + 1) = j + j * h := by ring
  rw [heq] at hh ⊢
  rw [K.area_at_column_index j h (by have := K.two_le; lia) hh, K.source_area_jump]

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

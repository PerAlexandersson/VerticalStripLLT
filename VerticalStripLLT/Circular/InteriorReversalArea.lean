import VerticalStripLLT.Circular.InteriorColumnReversal
import VerticalStripLLT.Circular.ReversalDecrement

/-! The smaller circular area sequence obtained by reversing an interior component. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped BigOperators Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- Apply the index decrement on the component and zero elsewhere. -/
noncomputable def reversalDecrement (v : Fin n) : ℕ :=
  if h : ∃ a : Fin (r + j), K.vertexEmbedding a = v then
    reversalDrop r j (Classical.choose h).val
  else 0

theorem reversalDecrement_vertex (a : Fin (r + j)) :
    K.reversalDecrement (K.vertex a.val) = reversalDrop r j a.val := by
  have h : ∃ b : Fin (r + j), K.vertexEmbedding b = K.vertex a.val := ⟨a, rfl⟩
  rw [reversalDecrement, dite_eq_left h]
  have heq : Classical.choose h = a :=
    K.vertexEmbedding.injective (Classical.choose_spec h)
  rw [heq]

theorem reversalDecrement_of_not_mem (v : Fin n) (hv : v ∉ K.componentVertices) :
    K.reversalDecrement v = 0 := by
  have hn : ¬ ∃ a : Fin (r + j), K.vertexEmbedding a = v := by
    rintro ⟨a, ha⟩
    exact hv ((K.mem_componentVertices_iff v).mpr ⟨a, ha⟩)
  exact dite_eq_right hn

theorem reversalDecrement_le_two (v : Fin n) : K.reversalDecrement v ≤ 2 := by
  unfold reversalDecrement
  split <;> simp_all [reversalDrop_le_two]

theorem reversalDecrement_next_ge (a : Fin (r + j)) (ha : a.val < r) :
    K.reversalDecrement (K.vertex a.val) ≤
      K.reversalDecrement (D.area.next (K.vertex a.val)) := by
  rw [K.next_jump _ ha, K.reversalDecrement_vertex a,
    K.reversalDecrement_vertex ⟨a.val + j, by lia⟩]
  exact reversalDrop_add_jump_le (by have := K.two_le; lia)

/-- The prescribed area values, before packaging their cyclic inequality. -/
noncomputable def reversalAreaValues (v : Fin n) : ℕ :=
  D.area.area v - K.reversalDecrement v

theorem reversalAreaValues_le (v : Fin n) : K.reversalAreaValues v ≤ D.area.area v :=
  Nat.sub_le _ _

theorem root_next_area_lt : D.area.area (D.area.next (K.vertex r)) <
    D.area.area (K.vertex r) := by
  have hg := K.root_eligible.boundary_gap D
  rw [Diagram.boundary, Diagram.boundary, D.residue_succ, ← K.root] at hg
  lia

theorem reversalAreaValues_cyclic (v : Fin n) :
    K.reversalAreaValues (D.area.next v) ≤ K.reversalAreaValues v + 1 := by
  have hcyc := D.area.cyclic v
  change D.area.area (D.area.next v) ≤ D.area.area v + 1 at hcyc
  by_cases hz : K.reversalDecrement v = 0
  · dsimp only [reversalAreaValues]
    rw [hz, Nat.sub_zero]
    exact (Nat.sub_le _ _).trans hcyc
  have hv : v ∈ K.componentVertices := by
    by_contra hv
    exact hz (K.reversalDecrement_of_not_mem v hv)
  obtain ⟨a, rfl⟩ := (K.mem_componentVertices_iff v).mp hv
  by_cases ha : a.val < r
  · have hnext := K.reversalDecrement_next_ge a ha
    dsimp only [reversalAreaValues]
    lia
  have hj := K.two_le
  have hjr := K.jump_lt
  have hapos : 0 < a.val := by lia
  obtain ⟨e, he, _, heh⟩ := K.exists_strict_edge a.val hapos a.isLt
  have hcorner := (D.strict_corner e he).2
  rw [heh] at hcorner
  have hd := K.reversalDecrement_le_two (K.vertex a.val)
  by_cases htwo : K.reversalDecrement (K.vertex a.val) = 2
  · have hdrop : reversalDrop r j a.val = 2 := by
      rwa [K.reversalDecrement_vertex a] at htwo
    have har : a.val = r :=
      reversalDrop_endpoint_two (by lia) hjr (by lia) a.isLt hdrop
    have hroot := K.root_next_area_lt
    rw [har] at hcyc htwo ⊢
    dsimp only [reversalAreaValues]
    rw [htwo]
    lia
  · dsimp only [reversalAreaValues]
    lia

/-- The actual smaller circular area sequence. -/
noncomputable def reversalArea : CircularArea n where
  positive := D.area.positive
  area := K.reversalAreaValues
  bound v := (K.reversalAreaValues_le v).trans_lt (D.area.bound v)
  cyclic v := K.reversalAreaValues_cyclic v

theorem reversalArea_root_lt : K.reversalArea.area (K.vertex r) <
    D.area.area (K.vertex r) := by
  have hj := K.two_le
  have hjr := K.jump_lt
  have hpos := K.root_eligible.2.1
  rw [← K.root] at hpos
  have hd := reversalDrop_root_pos (by lia : 0 < j) hjr
  change D.area.area (K.vertex r) - K.reversalDecrement (K.vertex r) < _
  rw [K.reversalDecrement_vertex ⟨r, by lia⟩]
  lia

theorem reversalArea_sum_lt : (∑ v, K.reversalArea.area v) < ∑ v, D.area.area v := by
  apply Finset.sum_lt_sum
  · intro v _
    exact K.reversalAreaValues_le v
  · exact ⟨K.vertex r, Finset.mem_univ _, K.reversalArea_root_lt⟩

/-- All rows of the merged component originally contain at least two cells. -/
theorem area_vertex_ge_two (a : Fin (r + j)) : 2 ≤ D.area.area (K.vertex a.val) := by
  by_cases hz : a.val = 0
  · rw [hz]
    exact K.source_area_ge_two
  by_cases ha : a.val ≤ r
  · exact K.area_ge_two_of_positive_main a.val (by lia) ha
  have hj := K.two_le
  have hjr := K.jump_lt
  have hal := a.isLt
  have hbase := K.area_ge_two_of_positive_main (a.val - j) (by lia) (by lia)
  have heq := K.area_jump (a.val - j) (by lia) (by lia)
  rw [Nat.sub_add_cancel (show j ≤ a.val by lia)] at heq
  rwa [heq]

/-- Every component row stays positive under its prescribed decrement. -/
theorem reversalArea_vertex_pos (a : Fin (r + j)) :
    0 < K.reversalArea.area (K.vertex a.val) := by
  have hj := K.two_le
  have hal := a.isLt
  have harea := K.area_vertex_ge_two a
  have hd := reversalDrop_le_two r j a.val
  change 0 < D.area.area (K.vertex a.val) - K.reversalDecrement (K.vertex a.val)
  rw [K.reversalDecrement_vertex a]
  by_cases htwo : reversalDrop r j a.val = 2
  · obtain ⟨hap, hmod, _⟩ := reversalDrop_two_iff.mp htwo
    have hdecomp := Nat.mod_add_div a.val j
    rw [hmod, Nat.zero_add] at hdecomp
    have hq : 0 < a.val / j := by
      by_contra hn
      have hz : a.val / j = 0 := by lia
      rw [hz, Nat.mul_zero] at hdecomp
      lia
    have haform : a.val = j * (a.val / j - 1 + 1) := by
      rw [Nat.sub_add_cancel hq]
      exact hdecomp.symm
    have hprofile := K.area_zero_column_succ (a.val / j - 1) (by rwa [← haform])
    rw [← haform] at hprofile
    have hs := K.source_area_ge_two
    lia
  · lia

/-- Existing strict heads remain at positive height. -/
theorem reversalArea_pos_of_strict (e : Edge D.area) (he : e ∈ D.strict) :
    0 < K.reversalArea.area e.head := by
  by_cases hm : e.head ∈ K.componentVertices
  · obtain ⟨a, hh⟩ := (K.mem_componentVertices_iff e.head).mp hm
    rw [← hh]
    exact K.reversalArea_vertex_pos a
  · have hz := K.reversalDecrement_of_not_mem e.head hm
    change 0 < D.area.area e.head - K.reversalDecrement e.head
    rw [hz, Nat.sub_zero, ← (D.strict_corner e he).1]
    exact e.length_pos

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

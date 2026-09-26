import VerticalStripLLT.Circular.InteriorReversalArea
import VerticalStripLLT.Circular.DiagramFromHeads
import VerticalStripLLT.Circular.GeometricArea

/-! A valid decorated target of strictly smaller half-square area. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped BigOperators Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- Column reversal moves the nonstrict source to the last row of its column. -/
def newSource : Fin n := K.vertex (reversalSourceIndex r j)

include K in
private theorem sourceIndex_eq_root (hr : r % j = 0) :
    reversalSourceIndex r j = r := by
  have hj : 0 < j := by have := K.two_le; lia
  have hmod := reversalSourceIndex_mod (r := r) hj
  have hlo := reversalSourceIndex_ge (r := r) hj
  have hhi := reversalSourceIndex_lt_add (r := r) hj
  have hdvd : j ∣ reversalSourceIndex r j - r :=
    (Nat.modEq_iff_dvd' hlo).mp (hr.trans hmod.symm)
  have hz := Nat.eq_zero_of_dvd_of_lt hdvd (show reversalSourceIndex r j - r < j by lia)
  lia

/-- Every retained old corner is still a corner after the area decreases. -/
theorem reversalArea_corner_of_old (v : Fin n)
    (hc : D.area.area (D.area.next v) ≤ D.area.area v) (hne : v ≠ K.newSource) :
    K.reversalArea.area (K.reversalArea.next v) ≤ K.reversalArea.area v := by
  change D.area.area (D.area.next v) - K.reversalDecrement (D.area.next v) ≤
    D.area.area v - K.reversalDecrement v
  by_cases hz : K.reversalDecrement v = 0
  · rw [hz, Nat.sub_zero]
    exact (Nat.sub_le _ _).trans hc
  have hv : v ∈ K.componentVertices := by
    by_contra hv
    exact hz (K.reversalDecrement_of_not_mem v hv)
  obtain ⟨a, rfl⟩ := (K.mem_componentVertices_iff v).mp hv
  by_cases ha : a.val < r
  · have hnext := K.reversalDecrement_next_ge a ha
    lia
  have hj : 0 < j := by have := K.two_le; lia
  have hjr := K.jump_lt
  have hd := K.reversalDecrement_le_two (K.vertex a.val)
  have hdrop : 0 < reversalDrop r j a.val := by
    rw [← K.reversalDecrement_vertex a]
    lia
  have har : a.val = r := by
    rcases reversalDrop_endpoint_pos hj hjr (by lia) a.isLt hdrop with har | hae
    · exact har
    · exact (hne (congrArg K.vertex hae)).elim
  have hnot : K.reversalDecrement (K.vertex a.val) ≠ 2 := by
    intro heq
    rw [K.reversalDecrement_vertex a] at heq
    have hrmod := (reversalDrop_two_iff.mp heq).2.2
    have hsource := K.sourceIndex_eq_root hrmod
    apply hne
    change K.vertex a.val = K.vertex (reversalSourceIndex r j)
    rw [har, hsource]
  have hroot := K.root_next_area_lt
  have heq : K.vertex a.val = K.vertex r := congrArg K.vertex har
  rw [← heq] at hroot
  lia

/-- The old source becomes a positive strict corner in the new diagram. -/
theorem reversalArea_source_corner :
    K.reversalArea.area (K.reversalArea.next (K.vertex 0)) ≤
      K.reversalArea.area (K.vertex 0) := by
  have hj := K.two_le
  have hjr := K.jump_lt
  change K.reversalAreaValues (D.area.next (K.vertex 0)) ≤ K.reversalAreaValues (K.vertex 0)
  rw [K.next_jump 0 (by lia), Nat.zero_add]
  dsimp only [reversalAreaValues]
  rw [K.reversalDecrement_vertex ⟨j, by lia⟩,
    K.reversalDecrement_vertex ⟨0, by lia⟩, K.source_area_jump]
  have hpos := K.source_area_ge_two
  by_cases hs : r % j = 0 <;>
    simp [reversalDrop, hs, show j ≠ 0 by lia]

theorem source_not_old_heads : K.vertex 0 ∉ D.strict.image Edge.head := by
  rintro h
  obtain ⟨e, he, hh⟩ := Finset.mem_image.mp h
  apply K.source_free e.tail
  exact ⟨e, Finset.mem_union_left _ he, rfl, hh⟩

theorem newSource_mem_old_heads : K.newSource ∈ D.strict.image Edge.head := by
  have hj : 0 < j := by have := K.two_le; lia
  obtain ⟨e, he, _, hh⟩ := K.exists_strict_edge (reversalSourceIndex r j)
    (reversalSourceIndex_pos hj K.jump_lt) (reversalSourceIndex_lt_add hj)
  exact Finset.mem_image.mpr ⟨e, he, hh⟩

/-- Replace the last column-zero strict head by the old source. -/
noncomputable def reversalHeads : Finset (Fin n) :=
  insert (K.vertex 0) ((D.strict.image Edge.head).erase K.newSource)

theorem reversalHeads_pos (v : Fin n) (hv : v ∈ K.reversalHeads) :
    0 < K.reversalArea.area v := by
  rcases Finset.mem_insert.mp hv with hsrc | hold
  · rw [hsrc]
    exact K.reversalArea_vertex_pos ⟨0, by have := K.two_le; lia⟩
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hold).2
    exact K.reversalArea_pos_of_strict e he

theorem reversalHeads_corner (v : Fin n) (hv : v ∈ K.reversalHeads) :
    K.reversalArea.area (K.reversalArea.next v) ≤ K.reversalArea.area v := by
  rcases Finset.mem_insert.mp hv with hsrc | hold
  · rw [hsrc]
    exact K.reversalArea_source_corner
  · obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hold
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact K.reversalArea_corner_of_old e.head (D.strict_corner e he).2 hne

theorem reversalHeads_card : K.reversalHeads.card = D.strict.card := by
  have hnot : K.vertex 0 ∉ (D.strict.image Edge.head).erase K.newSource :=
    fun h => K.source_not_old_heads (Finset.mem_erase.mp h).2
  rw [reversalHeads, Finset.card_insert_of_notMem hnot,
    Finset.card_erase_add_one K.newSource_mem_old_heads]
  apply Finset.card_image_of_injOn
  intro e he f hf hh
  exact D.strict_edge_eq_of_head_eq he hf hh

/-- The explicit smaller decorated path for every merged interior component. -/
noncomputable def reversalTarget : Diagram n :=
  Diagram.fromHeads K.reversalArea K.reversalHeads K.reversalHeads_pos K.reversalHeads_corner

theorem reversalTarget_area : K.reversalTarget.area = K.reversalArea := rfl

theorem reversalTarget_strict_card : K.reversalTarget.strict.card = D.strict.card := by
  rw [reversalTarget, Diagram.fromHeads_strict_card, K.reversalHeads_card]

theorem reversalTarget_doubledArea_lt : K.reversalTarget.doubledArea < D.doubledArea := by
  have hs := K.reversalArea_sum_lt
  have hc := K.reversalTarget.strict_card_le_area_sum
  rw [K.reversalTarget_strict_card] at hc
  change D.strict.card ≤ ∑ v, K.reversalArea.area v at hc
  rw [Diagram.doubledArea, Diagram.doubledArea, K.reversalTarget_strict_card]
  change 2 * (∑ v, K.reversalArea.area v) - D.strict.card <
    2 * (∑ v, D.area.area v) - D.strict.card
  lia

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

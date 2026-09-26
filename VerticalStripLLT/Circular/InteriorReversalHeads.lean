import VerticalStripLLT.Circular.InteriorReversalTarget
import VerticalStripLLT.Circular.InteriorColumnReversal

/-! Head-set bookkeeping for reversal of an isolated interior component. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

private theorem colLen_source (hj : 0 < j) :
    colLen (r + j) j 0 - 1 = (r + j - 1) / j := by
  have h : r + j + j - 1 = (r + j - 1) + j := by lia
  simp only [colLen, Nat.sub_zero, h, Nat.add_div_right _ hj, Nat.add_sub_cancel]

theorem reversalPerm_vertex_zero :
    K.reversalPerm (K.vertex 0) = K.newSource := by
  have hj : 0 < j := by have := K.two_le; lia
  rw [K.reversalPerm_vertex ⟨0, by have := K.two_le; lia⟩]
  simp only [Nat.zero_mod, Nat.zero_div]
  rw [show columnReverseIndex (r + j) j 0 0 = j * (colLen (r + j) j 0 - 1) by
    simp [columnReverseIndex]]
  rw [colLen_source hj]
  rfl

theorem reversalPerm_newSource :
    K.reversalPerm K.newSource = K.vertex 0 := by
  rw [← K.reversalPerm_vertex_zero, K.reversalPerm_involutive]

theorem reversalPerm_mem_component_iff (v : Fin n) :
    K.reversalPerm v ∈ K.componentVertices ↔ v ∈ K.componentVertices := by
  constructor
  · intro hv
    by_contra hn
    have hfix := K.reversalPerm_fixed v hn
    exact hn (by simpa [hfix] using hv)
  · intro hv
    obtain ⟨a, rfl⟩ := K.mem_componentVertices_iff v |>.mp hv
    apply (K.mem_componentVertices_iff _).mpr
    rw [K.reversalPerm_vertex a]
    exact ⟨columnReverseFin (r + j) j (by have := K.two_le; lia) a, rfl⟩

theorem component_head_mem_iff (a : Fin (r + j)) :
    K.vertex a ∈ D.strict.image Edge.head ↔ 0 < a.val := by
  constructor
  · intro h
    obtain ⟨e, he, hh⟩ := Finset.mem_image.mp h
    by_contra hz
    have ha : a.val = 0 := by lia
    apply K.source_free e.tail
    exact ⟨e, Finset.mem_union_left _ he, rfl, hh.trans (by rw [ha])⟩
  · intro ha
    obtain ⟨e, he, _, hh⟩ := K.exists_strict_edge a.val ha a.isLt
    exact Finset.mem_image.mpr ⟨e, he, hh⟩

theorem old_head_mem_component_iff (v : Fin n) (hv : v ∈ K.componentVertices) :
    v ∈ D.strict.image Edge.head ↔ v ≠ K.vertex 0 := by
  obtain ⟨a, rfl⟩ := K.mem_componentVertices_iff v |>.mp hv
  constructor
  · intro h ha
    rw [ha] at h
    exact K.source_not_old_heads h
  · intro ha
    have hapos : 0 < a.val := by
      by_contra hz
      have : a.val = 0 := by lia
      apply ha
      rw [this]
    exact (K.component_head_mem_iff a).mpr hapos

private theorem source_ne_newSource : K.vertex 0 ≠ K.newSource := by
  intro h
  apply K.source_not_old_heads
  rw [h]
  exact K.newSource_mem_old_heads

theorem reversalHeads_mem_iff (v : Fin n) :
    v ∈ K.reversalHeads ↔ K.reversalPerm v ∈ D.strict.image Edge.head := by
  by_cases hv : v ∈ K.componentVertices
  · have hp : K.reversalPerm v ∈ K.componentVertices :=
      (K.reversalPerm_mem_component_iff v).mpr hv
    have hleft : v ∈ K.reversalHeads ↔ v ≠ K.newSource := by
      rw [reversalHeads]
      constructor
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · intro heq
          exact K.source_ne_newSource (h.symm.trans heq)
        · exact (Finset.mem_erase.mp h).1
      · intro h
        by_cases hs : v = K.vertex 0
        · exact Finset.mem_insert.mpr (Or.inl hs)
        · apply Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h,
            (K.old_head_mem_component_iff v hv).mpr hs⟩))
    rw [hleft, K.old_head_mem_component_iff (K.reversalPerm v) hp]
    constructor
    · intro h hz
      apply h
      calc
        v = K.reversalPerm (K.reversalPerm v) :=
          (K.reversalPerm_involutive v).symm
        _ = K.reversalPerm (K.vertex 0) := by rw [hz]
        _ = K.newSource := K.reversalPerm_vertex_zero
    · intro h hz
      apply h
      calc
        K.reversalPerm v = K.reversalPerm (K.newSource) := by rw [hz]
        _ = K.vertex 0 := K.reversalPerm_newSource
  · have hp : K.reversalPerm v = v := K.reversalPerm_fixed v hv
    have h0 : v ≠ K.vertex 0 := by
      intro h
      apply hv
      rw [h]
      exact (K.mem_componentVertices_iff _).mpr ⟨⟨0, by have := K.two_le; lia⟩, rfl⟩
    have hs : v ≠ K.newSource := by
      intro h
      apply hv
      rw [h]
      exact (K.mem_componentVertices_iff _).mpr ⟨⟨reversalSourceIndex r j,
        reversalSourceIndex_lt_add (by have := K.two_le; lia)⟩, rfl⟩
    rw [hp, reversalHeads]
    simp only [Finset.mem_insert, Finset.mem_erase]
    simp [hs, h0]

theorem reversalHeads_eq_image :
    K.reversalHeads = (D.strict.image Edge.head).image K.reversalPerm := by
  ext v
  rw [K.reversalHeads_mem_iff v]
  constructor
  · intro hv
    exact Finset.mem_image.mpr ⟨K.reversalPerm v, hv, K.reversalPerm_involutive v⟩
  · intro hv
    obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hv
    rw [← hwp, K.reversalPerm_involutive]
    exact hw

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

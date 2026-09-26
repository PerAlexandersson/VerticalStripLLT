import VerticalStripLLT.Circular.InteriorMergedComponent

/-! The merged strict path is an isolated component of the strict graph. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} {r j : ℕ}

namespace InteriorMergedComponent

variable (K : InteriorMergedComponent D t r j)

/-- The only selected predecessor of an interior component vertex. -/
theorem selected_to_vertex_iff {a : ℕ} (ha : a < r + j) (u : Fin n) :
    D.edgeData.selected ∅ u (K.vertex a) ↔
      0 < a ∧ u = K.vertex (a - 1) := by
  constructor
  · intro huv
    have hapos : 0 < a := by
      by_contra hzero
      have : a = 0 := by lia
      subst this
      exact K.source_free u huv
    have hprev : D.edgeData.selected ∅ (K.vertex (a - 1)) (K.vertex a) := by
      simpa [Nat.sub_add_cancel hapos] using K.step (a - 1) (by lia)
    refine ⟨hapos, ?_⟩
    exact (D.strict_selected_leftUnique hprev huv).symm
  · rintro ⟨hapos, rfl⟩
    simpa [Nat.sub_add_cancel hapos] using K.step (a - 1) (by lia)

/-- The only selected successor of an interior component vertex. -/
theorem selected_from_vertex_iff {a : ℕ} (ha : a < r + j) (v : Fin n) :
    D.edgeData.selected ∅ (K.vertex a) v ↔
      a + 1 < r + j ∧ v = K.vertex (a + 1) := by
  constructor
  · intro huv
    have hlast : a + 1 < r + j := by
      by_contra hlast
      have heq : a = r + j - 1 := by lia
      subst heq
      exact K.sink_free v huv
    have hnext : D.edgeData.selected ∅ (K.vertex a) (K.vertex (a + 1)) :=
      K.step a hlast
    refine ⟨hlast, ?_⟩
    exact (D.strict_selected_rightUnique hnext huv).symm
  · rintro ⟨ha1, rfl⟩
    exact K.step a ha1

/-- The finite embedding of the merged component's vertices. -/
def vertexEmbedding : Fin (r + j) ↪ Fin n where
  toFun a := K.vertex a.val
  inj' a b hab := Fin.ext (K.injective a.isLt b.isLt hab)

include K in
theorem size_le : r + j ≤ n := by
  have h := Fintype.card_le_of_injective K.vertexEmbedding K.vertexEmbedding.injective
  simpa using h

/-- The set of vertices belonging to the merged component. -/
def componentVertices : Finset (Fin n) := Finset.univ.map K.vertexEmbedding

theorem mem_componentVertices_iff (v : Fin n) :
    v ∈ K.componentVertices ↔ ∃ a : Fin (r + j), K.vertex a = v := by
  simp [componentVertices, vertexEmbedding]

/-- Every selected edge entering the component comes from the component. -/
theorem selected_into_component (u v : Fin n) (hv : v ∈ K.componentVertices)
    (h : D.edgeData.selected ∅ u v) : u ∈ K.componentVertices := by
  obtain ⟨a, rfl⟩ := K.mem_componentVertices_iff v |>.mp hv
  rw [K.selected_to_vertex_iff a.isLt u] at h
  obtain ⟨ha, rfl⟩ := h
  apply (K.mem_componentVertices_iff _).mpr
  exact ⟨⟨a - 1, by lia⟩, rfl⟩

/-- Every selected edge leaving the component ends in the component. -/
theorem selected_from_component (u v : Fin n) (hu : u ∈ K.componentVertices)
    (h : D.edgeData.selected ∅ u v) : v ∈ K.componentVertices := by
  obtain ⟨a, rfl⟩ := K.mem_componentVertices_iff u |>.mp hu
  rw [K.selected_from_vertex_iff a.isLt v] at h
  obtain ⟨ha, rfl⟩ := h
  apply (K.mem_componentVertices_iff _).mpr
  exact ⟨⟨a + 1, ha⟩, rfl⟩

end InteriorMergedComponent

end VerticalStripLLT.Circular.Diagram

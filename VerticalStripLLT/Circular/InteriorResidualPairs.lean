import VerticalStripLLT.Circular.InteriorExteriorPairs

/-! Exterior pair sets under reversal of an isolated component. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

noncomputable def exteriorNormalPairs (D : Diagram n) (C : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  D.pairGraph.normalEdges.filter (fun p => p.1 ∉ C ∨ p.2 ∉ C)

theorem exteriorNormalPairs_subset_normal (D : Diagram n) (C : Finset (Fin n)) :
    D.exteriorNormalPairs C ⊆ D.pairGraph.normalEdges := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

namespace InteriorMergedComponent

variable {r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

theorem strictPairs_eq_map :
    K.reversalTarget.pairGraph.strictEdges =
      D.pairGraph.strictEdges.map (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, rfl⟩ := (Equiv.prodCongr K.reversalPerm K.reversalPerm).surjective p
    rcases q with ⟨u, v⟩
    exact Finset.mem_map.mpr ⟨(u, v),
      (K.strictPairs_reversal_iff u v).mp hp, rfl⟩
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    rcases q with ⟨u, v⟩
    exact (K.strictPairs_reversal_iff u v).mpr hq

theorem exteriorNormalPairs_reversal_iff (u v : Fin n) :
    (K.reversalPerm u, K.reversalPerm v) ∈
        K.reversalTarget.exteriorNormalPairs K.componentVertices ↔
      (u, v) ∈ D.exteriorNormalPairs K.componentVertices := by
  simp only [exteriorNormalPairs, Finset.mem_filter, K.reversalPerm_mem_component_iff]
  constructor
  · rintro ⟨hp, hout⟩
    exact ⟨(K.normalPairs_reversal_iff u v hout).mp hp, hout⟩
  · rintro ⟨hp, hout⟩
    exact ⟨(K.normalPairs_reversal_iff u v hout).mpr hp, hout⟩

theorem exteriorNormalPairs_eq_map :
    K.reversalTarget.exteriorNormalPairs K.componentVertices =
      (D.exteriorNormalPairs K.componentVertices).map
        (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, rfl⟩ := (Equiv.prodCongr K.reversalPerm K.reversalPerm).surjective p
    rcases q with ⟨u, v⟩
    exact Finset.mem_map.mpr ⟨(u, v),
      (K.exteriorNormalPairs_reversal_iff u v).mp hp, rfl⟩
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    rcases q with ⟨u, v⟩
    exact (K.exteriorNormalPairs_reversal_iff u v).mpr hq

end InteriorMergedComponent
end VerticalStripLLT.Circular.Diagram

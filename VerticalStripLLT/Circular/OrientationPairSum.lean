import VerticalStripLLT.Circular.HRVTriangle
import VerticalStripLLT.Circular.OrientationSum
import VerticalStripLLT.Circular.NaturalPairSwap

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

theorem transGen_of_transGen_steps {S1 S2 : ℤ → ℤ → Prop}
    (h : ∀ x y, S1 x y → Relation.TransGen S2 x y) {x y : ℤ}
    (hxy : Relation.TransGen S1 x y) : Relation.TransGen S2 x y := by
  induction hxy with
  | single hs => exact h _ _ hs
  | tail _ hs ih => exact ih.trans (h _ _ hs)

namespace Diagram

variable {n : ℕ} (D : Diagram n)

noncomputable def normalOf (Q : Finset (Fin n × Fin n)) : Finset (Edge D.area) :=
  D.edgeData.normalEdges.filter fun ε => (ε.tail, ε.head) ∈ Q

def pairStep (P : Finset (Fin n × Fin n)) (x y : ℤ) : Prop :=
  (D.residue x, D.residue y) ∈ P ∧ 0 < y - x ∧ y - x < n

theorem pairStep_congr (D' : Diagram n) (P : Finset (Fin n × Fin n)) (x y : ℤ) :
    D.pairStep P x y ↔ D'.pairStep P x y := Iff.rfl

theorem normalOf_subset (Q : Finset (Fin n × Fin n)) :
    D.normalOf Q ⊆ D.edgeData.normalEdges := Finset.filter_subset _ _

theorem mem_normalOf_iff (Q : Finset (Fin n × Fin n)) (ε : Edge D.area) :
    ε ∈ D.normalOf Q ↔ ε ∉ D.strict ∧ (ε.tail, ε.head) ∈ Q := by
  simp only [normalOf, Finset.mem_filter, mem_normalEdges_iff]

theorem normalOf_insert (Q : Finset (Fin n × Fin n)) {ε : Edge D.area}
    (hε : ε ∉ D.strict) :
    D.normalOf (insert (ε.tail, ε.head) Q) = insert ε (D.normalOf Q) := by
  ext δ
  simp only [mem_normalOf_iff, Finset.mem_insert]
  constructor
  · rintro ⟨hδ, h | h⟩
    · exact Or.inl (D.endpointEmbedding.injective h)
    · exact Or.inr ⟨hδ, h⟩
  · rintro (rfl | ⟨hδ, h⟩)
    · exact ⟨hε, Or.inl rfl⟩
    · exact ⟨hδ, Or.inr h⟩

theorem normalOf_map (A : Finset (Edge D.area)) (hA : A ⊆ D.edgeData.normalEdges) :
    D.normalOf (A.map D.endpointEmbedding) = A := by
  ext ε
  rw [normalOf, Finset.mem_filter]
  change ε ∈ D.edgeData.normalEdges ∧
    D.endpointEmbedding ε ∈ A.map D.endpointEmbedding ↔ _
  rw [Finset.mem_map' D.endpointEmbedding]
  exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩

theorem map_normalOf (Q : Finset (Fin n × Fin n))
    (hQ : Q ⊆ D.pairGraph.normalEdges) :
    (D.normalOf Q).map D.endpointEmbedding = Q := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨ε, hε, rfl⟩
    exact (Finset.mem_filter.mp hε).2
  · intro hx
    obtain ⟨ε, hε, hp⟩ := (D.mem_pairGraph_normal_iff x).mp (hQ hx)
    refine ⟨ε, Finset.mem_filter.mpr ⟨hε, ?_⟩, hp⟩
    rw [hp]
    exact hx

theorem shiftedOrientationExpansion_eq_pairSum :
    shiftedOrientationExpansion D = ∑ Q ∈ D.pairGraph.normalEdges.powerset,
      MvPolynomial.C (Polynomial.X ^ Q.card) * D.orientMono (D.normalOf Q) := by
  rw [shiftedOrientationExpansion_eq_sum]
  apply Finset.sum_nbij' (fun A => A.map D.endpointEmbedding) (fun Q => D.normalOf Q)
  · intro A hA
    rw [Finset.mem_powerset] at hA ⊢
    exact Finset.map_subset_map.mpr hA
  · intro Q _
    rw [Finset.mem_powerset]
    exact D.normalOf_subset Q
  · intro A hA
    rw [Finset.mem_powerset] at hA
    exact D.normalOf_map A hA
  · intro Q hQ
    rw [Finset.mem_powerset] at hQ
    exact D.map_normalOf Q hQ
  · intro A hA
    rw [Finset.mem_powerset] at hA
    rw [Finset.card_map, D.normalOf_map A hA]

theorem liftStep_normalOf_iff (Q : Finset (Fin n × Fin n))
    (hQ : Q ⊆ D.pairGraph.normalEdges) (x y : ℤ) :
    D.liftStep (D.normalOf Q) x y ↔ D.pairStep (D.pairGraph.strictEdges ∪ Q) x y := by
  rw [liftStep_iff_endpoints, pairStep]
  constructor
  · rintro ⟨ε, hε, hx, hy, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    rw [← hx, ← hy]
    rcases Finset.mem_union.mp hε with h | h
    · exact Finset.mem_union_left _
        ((D.mem_pairGraph_strict_iff _).mpr ⟨ε, h, rfl⟩)
    · exact Finset.mem_union_right _ ((D.mem_normalOf_iff Q ε).mp h).2
  · rintro ⟨hmem, h1, h2⟩
    rcases Finset.mem_union.mp hmem with h | h
    · obtain ⟨ε, hε, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
      exact ⟨ε, Finset.mem_union_left _ hε, congrArg Prod.fst hp,
        congrArg Prod.snd hp, h1, h2⟩
    · obtain ⟨ε, hε, hp⟩ := (D.mem_pairGraph_normal_iff _).mp (hQ h)
      refine ⟨ε, Finset.mem_union_right _ ?_, congrArg Prod.fst hp,
        congrArg Prod.snd hp, h1, h2⟩
      rw [mem_normalOf_iff, ← mem_normalEdges_iff]
      exact ⟨hε, hp ▸ h⟩

theorem orientMono_normalOf_eq_of_transGen {D' : Diagram n}
    (Q : Finset (Fin n × Fin n)) (Q' : Finset (Fin n × Fin n))
    (hQ : Q ⊆ D.pairGraph.normalEdges) (hQ' : Q' ⊆ D'.pairGraph.normalEdges)
    (h1 : ∀ x y, D.pairStep (D.pairGraph.strictEdges ∪ Q) x y →
      Relation.TransGen (D'.pairStep (D'.pairGraph.strictEdges ∪ Q')) x y)
    (h2 : ∀ x y, D'.pairStep (D'.pairGraph.strictEdges ∪ Q') x y →
      Relation.TransGen (D.pairStep (D.pairGraph.strictEdges ∪ Q)) x y) :
    D.orientMono (D.normalOf Q) = D'.orientMono (D'.normalOf Q') := by
  apply orientMono_eq_of_transGen D (D.normalOf Q) (D'.normalOf Q')
    (D.normalOf_subset Q) (D'.normalOf_subset Q')
  have e1 : D.liftStep (D.normalOf Q) =
      D.pairStep (D.pairGraph.strictEdges ∪ Q) := by
    funext x y
    exact propext (D.liftStep_normalOf_iff Q hQ x y)
  have e2 : D'.liftStep (D'.normalOf Q') =
      D'.pairStep (D'.pairGraph.strictEdges ∪ Q') := by
    funext x y
    exact propext (D'.liftStep_normalOf_iff Q' hQ' x y)
  intro x y
  rw [e1, e2]
  exact ⟨transGen_of_transGen_steps h1, transGen_of_transGen_steps h2⟩

end Diagram
end VerticalStripLLT.Circular

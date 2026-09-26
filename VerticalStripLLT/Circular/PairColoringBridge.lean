import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Circular.EdgeLength
import VerticalStripLLT.Circular.PairColoring

/-! Identification of diagram edge colorings with the pair-graph coloring model. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- An edge is determined by its directed pair of circular endpoints. -/
def endpointEmbedding : Edge D.area ↪ Fin n × Fin n :=
  ⟨fun e => (e.tail, e.head), by
    intro e f h
    obtain ⟨ht, hh⟩ := Prod.mk.inj h
    apply Subtype.ext
    apply Prod.ext
    · exact hh
    · apply Fin.ext
      exact Edge.length_eq_of_endpoints ht hh⟩

/-- The pair graph obtained by forgetting the edge-instance labels of a diagram. -/
noncomputable def pairGraph : PairGraph n where
  normalEdges := D.edgeData.normalEdges.map D.endpointEmbedding
  strictEdges := D.strict.map D.endpointEmbedding

theorem mem_pairGraph_strict_iff (x : Fin n × Fin n) :
    x ∈ D.pairGraph.strictEdges ↔ ∃ e ∈ D.strict, (e.tail, e.head) = x := by
  change x ∈ D.strict.map D.endpointEmbedding ↔ _
  rw [Finset.mem_map]
  rfl

theorem mem_pairGraph_normal_iff (x : Fin n × Fin n) :
    x ∈ D.pairGraph.normalEdges ↔ ∃ e ∈ D.edgeData.normalEdges, (e.tail, e.head) = x := by
  change x ∈ D.edgeData.normalEdges.map D.endpointEmbedding ↔ _
  rw [Finset.mem_map]
  rfl

theorem pairGraph_admissible_iff {m : ℕ} (c : Fin n → Fin m) :
    PairGraph.admissible D.pairGraph c ↔ D.edgeData.admissibleColoring c := by
  constructor
  · intro h e he
    have h' := h (D.endpointEmbedding e) (Finset.mem_map_of_mem _ he)
    exact h'
  · intro h x hx
    rcases Finset.mem_map.mp hx with ⟨e, he, rfl⟩
    exact h e he

theorem pairGraph_ascentCount {m : ℕ} (c : Fin n → Fin m) :
    D.pairGraph.ascentCount c = (D.edgeData.ascentEdges c).card := by
  change ((D.edgeData.normalEdges.map D.endpointEmbedding).filter fun e =>
    c e.1 < c e.2).card =
      (D.edgeData.normalEdges.filter fun e => c (D.edgeData.tail e) < c (D.edgeData.head e)).card
  rw [Finset.filter_map, Finset.card_map]
  exact congrArg Finset.card (Finset.filter_congr fun e _ => Iff.rfl)

theorem pairGraph_coloringWeight {m : ℕ} (c : Fin n → Fin m) :
    D.pairGraph.coloringWeight c = D.edgeData.coloringWeight c := by
  unfold PairGraph.coloringWeight EdgeData.coloringWeight
  rw [D.pairGraph_admissible_iff, D.pairGraph_ascentCount]
  rfl

theorem pairGraph_coloringLLT (m : ℕ) :
    D.pairGraph.coloringLLT m = D.coloringLLT m := by
  unfold PairGraph.coloringLLT Diagram.coloringLLT EdgeData.coloringLLT
  apply Finset.sum_congr rfl
  intro c _
  exact D.pairGraph_coloringWeight c

end Diagram

end VerticalStripLLT.Circular

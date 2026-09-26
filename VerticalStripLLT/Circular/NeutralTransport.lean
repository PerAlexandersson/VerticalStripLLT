import VerticalStripLLT.Circular.StrictDepth
import VerticalStripLLT.Circular.NeutralRank
import VerticalStripLLT.Circular.StrictCycleVanishing

/-! The rank argument for a neutral exchange of strict chains.

`NeutralTransport` records graph and edge-length data, not a rank inequality.
The full bounce adapter must construct these data from the two contact paths.
-/

namespace VerticalStripLLT.Circular

open scoped BigOperators

namespace Diagram

abbrev StrictEdge {n : ℕ} (D : Diagram n) := {e : Edge D.area // e ∈ D.strict}

noncomputable def strictRank {n : ℕ} (D : Diagram n) : ℕ :=
  ∑ e : D.StrictEdge, ancestorDepth (D.edgeData.selected ∅) e.val.head * e.val.length.val

end Diagram

/-- Exact strict-graph and length data for a neutral bounce. -/
structure NeutralTransport {n : ℕ} (D D' : Diagram n) where
  vertices : Fin n ≃ Fin n
  edges : D.StrictEdge ≃ D'.StrictEdge
  tail_eq : ∀ e, (edges e).val.tail = vertices e.val.tail
  head_eq : ∀ e, (edges e).val.head = vertices e.val.head
  first : D.StrictEdge
  last : D.StrictEdge
  path : Relation.TransGen (D.edgeData.selected ∅) first.val.head last.val.head
  first_length : (edges first).val.length.val = first.val.length.val + 1
  last_length : (edges last).val.length.val + 1 = last.val.length.val
  other_length : ∀ e, e ≠ first → e ≠ last →
    (edges e).val.length.val = e.val.length.val

namespace NeutralTransport

variable {n : ℕ} {D D' : Diagram n} (T : NeutralTransport D D')

include T

set_option backward.isDefEq.respectTransparency false

theorem selected_iff (u v : Fin n) :
    D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (T.vertices u) (T.vertices v) := by
  simp only [EdgeData.selected, Diagram.edgeData, Finset.union_empty]
  constructor
  · rintro ⟨e, he, hu, hv⟩
    have hs : e ∈ D.strict := by simpa [Diagram.edgeData] using he
    refine ⟨(T.edges ⟨e, hs⟩).val, ?_, ?_, ?_⟩
    · exact (T.edges ⟨e, hs⟩).property
    · rw [T.tail_eq, hu]
    · rw [T.head_eq, hv]
  · rintro ⟨e, he, hu, hv⟩
    have hs : e ∈ D'.strict := by simpa [Diagram.edgeData] using he
    let f := T.edges.symm ⟨e, hs⟩
    have hf : T.edges f = ⟨e, hs⟩ := T.edges.apply_symm_apply _
    refine ⟨f.val, ?_, ?_, ?_⟩
    · exact f.property
    · apply T.vertices.injective
      rw [← T.tail_eq, hf]
      exact hu
    · apply T.vertices.injective
      rw [← T.head_eq, hf]
      exact hv

theorem acyclic (h : D.edgeData.Admissible ∅) : D'.edgeData.Admissible ∅ := by
  intro v hv
  have hp := Relation.TransGen.lift T.vertices.symm
    (fun a b hab => (T.selected_iff (T.vertices.symm a) (T.vertices.symm b)).mpr
      (by simpa using hab)) _ _ hv
  exact h _ hp

theorem rank_lt (h : D.edgeData.Admissible ∅) : D'.strictRank < D.strictRank := by
  apply weighted_edge_rank_drop T.edges
    (fun e => ancestorDepth (D.edgeData.selected ∅) e.val.head)
    (fun e => ancestorDepth (D'.edgeData.selected ∅) e.val.head)
    (fun e => e.val.length.val) (fun e => e.val.length.val)
    (eIn := T.first) (eOut := T.last)
  · intro e
    rw [T.head_eq]
    exact ancestorDepth_equiv _ _ T.vertices T.selected_iff _
  · exact ancestorDepth_lt_of_transGen _ h T.path
  · exact T.first_length
  · exact T.last_length
  · exact T.other_length

end NeutralTransport

/-- An infinite sequence of neutral transports cannot start with an acyclic strict graph. -/
theorem not_admissible_of_infinite_neutral_transport {n : ℕ} (D : ℕ → Diagram n)
    (step : ∀ i, Nonempty (NeutralTransport (D i) (D (i + 1)))) :
    ¬ (D 0).edgeData.Admissible ∅ := by
  intro h0
  have ha : ∀ i, (D i).edgeData.Admissible ∅ := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih => exact (Classical.choice (step i)).acyclic ih
  have hb : ∀ i, (D i).strictRank + i ≤ (D 0).strictRank := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hd := (Classical.choice (step i)).rank_lt (ha i)
      lia
  have := hb ((D 0).strictRank + 1)
  lia

/-- A strict cycle forces the entire coloring polynomial to vanish, for every alphabet. -/
theorem coloringLLT_eq_zero_of_infinite_neutral_transport {n : ℕ} (D : ℕ → Diagram n)
    (step : ∀ i, Nonempty (NeutralTransport (D i) (D (i + 1)))) (m : ℕ) :
    (D 0).coloringLLT m = 0 :=
  coloringLLT_eq_zero_of_not_admissible_empty (D 0)
    (not_admissible_of_infinite_neutral_transport D step) m

end VerticalStripLLT.Circular

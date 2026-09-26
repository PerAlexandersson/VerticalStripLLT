import VerticalStripLLT.Circular.NeutralContacts
import VerticalStripLLT.Circular.StrictEdgeEquiv

/-! Infinite full forward neutral bounces force a cycle of original strict edges. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

noncomputable def strictEdgeOfSelected {n : ℕ} (D : Diagram n) {u v : Fin n}
    (h : D.edgeData.selected ∅ u v) : D.StrictEdge :=
  ⟨Classical.choose h, by
    simpa [Diagram.edgeData] using (Classical.choose_spec h).1⟩

theorem strictEdgeOfSelected_tail {n : ℕ} (D : Diagram n) {u v : Fin n}
    (h : D.edgeData.selected ∅ u v) : (D.strictEdgeOfSelected h).val.tail = u :=
  (Classical.choose_spec h).2.1

theorem strictEdgeOfSelected_head {n : ℕ} (D : Diagram n) {u v : Fin n}
    (h : D.edgeData.selected ∅ u v) : (D.strictEdgeOfSelected h).val.head = v :=
  (Classical.choose_spec h).2.2

end Diagram

namespace FullNeutralBounce

variable {n : ℕ} {D D' : Diagram n} (B : FullNeutralBounce D D')

include B

set_option backward.isDefEq.respectTransparency false

noncomputable def firstEdge : D.StrictEdge := D.strictEdgeOfSelected B.start_step
noncomputable def lastEdge : D.StrictEdge := D.strictEdgeOfSelected B.end_step

@[simp] theorem firstEdge_tail : B.firstEdge.val.tail = B.main 0 :=
  D.strictEdgeOfSelected_tail B.start_step
@[simp] theorem firstEdge_head : B.firstEdge.val.head = B.inner 0 :=
  D.strictEdgeOfSelected_head B.start_step
@[simp] theorem lastEdge_tail : B.lastEdge.val.tail = B.inner (Fin.last B.k) :=
  D.strictEdgeOfSelected_tail B.end_step
@[simp] theorem lastEdge_head : B.lastEdge.val.head = B.main (Fin.last (B.k + 2)) :=
  D.strictEdgeOfSelected_head B.end_step

theorem permutation_inner (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.permutation ha (B.inner i) = B.parallel i :=
  pairedSwap_left _ _ _ _ _ i

theorem permutation_parallel (ha : D.edgeData.Admissible ∅) (i : Fin (B.k + 1)) :
    B.permutation ha (B.parallel i) = B.inner i :=
  pairedSwap_right _ _ _ _ _ i

theorem permutation_start (ha : D.edgeData.Admissible ∅) :
    B.permutation ha (B.main 0) = B.main 0 :=
  pairedSwap_fixed _ _ _ _ _ _ (B.start_not_mem_inner ha) (B.start_not_mem_parallel ha)

theorem permutation_end (ha : D.edgeData.Admissible ∅) :
    B.permutation ha (B.main (Fin.last (B.k + 2))) = B.main (Fin.last (B.k + 2)) :=
  pairedSwap_fixed _ _ _ _ _ _ (B.end_not_mem_inner ha) (B.end_not_mem_parallel ha)

noncomputable def edgeEquiv (ha : D.edgeData.Admissible ∅) :
    D.StrictEdge ≃ D'.StrictEdge :=
  Diagram.strictEdgeEquiv (B.permutation ha) (B.selected_iff ha)

theorem edgeEquiv_tail (ha : D.edgeData.Admissible ∅) (e : D.StrictEdge) :
    (B.edgeEquiv ha e).val.tail = B.permutation ha e.val.tail :=
  Diagram.strictEdgeEquiv_tail _ _ e

theorem edgeEquiv_head (ha : D.edgeData.Admissible ∅) (e : D.StrictEdge) :
    (B.edgeEquiv ha e).val.head = B.permutation ha e.val.head :=
  Diagram.strictEdgeEquiv_head _ _ e

theorem endpoint_path :
    Relation.TransGen (D.edgeData.selected ∅) B.firstEdge.val.head B.lastEdge.val.head := by
  rw [B.firstEdge_head, B.lastEdge_head]
  have h := walk_transGen_of_lt (D.edgeData.selected ∅) B.main B.main_steps B.k 1
    (by lia)
  convert h using 1
  congr 1
  apply Fin.ext
  simp [Fin.last]
  lia

theorem first_length (ha : D.edgeData.Admissible ∅) :
    (B.edgeEquiv ha B.firstEdge).val.length.val = B.firstEdge.val.length.val + 1 := by
  apply Edge.length_succ_of_next_head
  · rw [B.edgeEquiv_tail, B.firstEdge_tail, B.permutation_start]
  · rw [B.edgeEquiv_head, B.firstEdge_head, B.permutation_inner]
    exact B.parallel_next 0

theorem last_length (ha : D.edgeData.Admissible ∅) :
    (B.edgeEquiv ha B.lastEdge).val.length.val + 1 = B.lastEdge.val.length.val := by
  apply Edge.length_succ_of_next_tail
  · rw [B.edgeEquiv_tail, B.lastEdge_tail, B.permutation_inner]
    exact B.parallel_next _
  · rw [B.edgeEquiv_head, B.lastEdge_head, B.permutation_end]

theorem other_length (ha : D.edgeData.Admissible ∅) (e : D.StrictEdge)
    (hfirst : e ≠ B.firstEdge) (hlast : e ≠ B.lastEdge) :
    (B.edgeEquiv ha e).val.length.val = e.val.length.val := by
  have he : D.edgeData.selected ∅ e.val.tail e.val.head :=
    ⟨e.val, by simp [Diagram.edgeData, e.property], rfl, rfl⟩
  rcases neutralExchange_source_edge_cases (D.edgeData.selected ∅)
    D.strict_selected_leftUnique D.strict_selected_rightUnique
    (B.main 0) (B.main (Fin.last (B.k + 2))) B.inner B.parallel B.start_step B.end_step
    B.inner_steps B.parallel_steps B.parallel_start B.parallel_end he with h | h | h | h | h
  · apply False.elim
    apply hfirst
    apply Subtype.ext
    exact D.strict_edge_eq_of_tail_eq e.property B.firstEdge.property
      (h.1.trans B.firstEdge_tail.symm)
  · apply False.elim
    apply hlast
    apply Subtype.ext
    exact D.strict_edge_eq_of_tail_eq e.property B.lastEdge.property
      (h.1.trans B.lastEdge_tail.symm)
  · obtain ⟨i, ht, hh⟩ := h
    apply Edge.length_eq_of_next_both
    · rw [B.edgeEquiv_tail, ht, B.permutation_inner]
      exact B.parallel_next _
    · rw [B.edgeEquiv_head, hh, B.permutation_inner]
      exact B.parallel_next _
  · obtain ⟨i, ht, hh⟩ := h
    symm
    apply Edge.length_eq_of_next_both
    · change e.val.tail = D.area.next (B.edgeEquiv ha e).val.tail
      rw [B.edgeEquiv_tail, ht, B.permutation_parallel]
      exact B.parallel_next _
    · change e.val.head = D.area.next (B.edgeEquiv ha e).val.head
      rw [B.edgeEquiv_head, hh, B.permutation_parallel]
      exact B.parallel_next _
  · apply Edge.length_eq_of_endpoints
    · rw [B.edgeEquiv_tail]
      exact pairedSwap_fixed _ _ _ _ _ _ h.1 h.2.1
    · rw [B.edgeEquiv_head]
      exact pairedSwap_fixed _ _ _ _ _ _ h.2.2.1 h.2.2.2

/-- Construct the rank transport from the explicit full-bounce contacts. -/
noncomputable def transport (ha : D.edgeData.Admissible ∅) : NeutralTransport D D' where
  vertices := B.permutation ha
  edges := B.edgeEquiv ha
  tail_eq := B.edgeEquiv_tail ha
  head_eq := B.edgeEquiv_head ha
  first := B.firstEdge
  last := B.lastEdge
  path := B.endpoint_path
  first_length := B.first_length ha
  last_length := B.last_length ha
  other_length := B.other_length ha

theorem preserves_acyclic (ha : D.edgeData.Admissible ∅) : D'.edgeData.Admissible ∅ :=
  (B.transport ha).acyclic ha

theorem strictRank_lt (ha : D.edgeData.Admissible ∅) : D'.strictRank < D.strictRank :=
  (B.transport ha).rank_lt ha

end FullNeutralBounce

/-- Indefinite forward neutral rewriting forces a strict cycle in the initial diagram. -/
theorem not_admissible_of_infinite_full_neutral_bounce {n : ℕ} (D : ℕ → Diagram n)
    (step : ∀ i, Nonempty (FullNeutralBounce (D i) (D (i + 1)))) :
    ¬ (D 0).edgeData.Admissible ∅ := by
  intro h0
  have ha : ∀ i, (D i).edgeData.Admissible ∅ := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih => exact (Classical.choice (step i)).preserves_acyclic ih
  exact not_admissible_of_infinite_neutral_transport D
    (fun i => ⟨(Classical.choice (step i)).transport (ha i)⟩) h0

theorem strict_cycle_of_infinite_full_neutral_bounce {n : ℕ} (D : ℕ → Diagram n)
    (step : ∀ i, Nonempty (FullNeutralBounce (D i) (D (i + 1)))) :
    ∃ v, Relation.TransGen ((D 0).edgeData.selected ∅) v v := by
  classical
  have h := not_admissible_of_infinite_full_neutral_bounce D step
  simpa only [EdgeData.Admissible, not_forall, not_not] using h

/-- The whole LLT vanishes in every finite alphabet if forward neutral bounces continue forever. -/
theorem coloringLLT_eq_zero_of_infinite_full_neutral_bounce {n : ℕ} (D : ℕ → Diagram n)
    (step : ∀ i, Nonempty (FullNeutralBounce (D i) (D (i + 1)))) (m : ℕ) :
    (D 0).coloringLLT m = 0 :=
  coloringLLT_eq_zero_of_not_admissible_empty (D 0)
    (not_admissible_of_infinite_full_neutral_bounce D step) m

end VerticalStripLLT.Circular

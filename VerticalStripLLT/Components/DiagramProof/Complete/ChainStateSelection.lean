import VerticalStripLLT.Components.DiagramProof.Complete.Chords

/-! Exact selected-edge formulas for complete chain states. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- A complete chain state consists of the root edge, all positive adjacent
edges, and the prescribed additional edges. -/
theorem completeChainState_selected_iff {n : ℕ} (hn : 0 < n)
    (S : Finset (Edge (completeDiagram n).area)) (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (completeChainState n S).val u v ↔
      (u = 0 ∧ v = Fin.last n) ∨
        (0 < u.val ∧ u.val + 1 = v.val) ∨
        (∃ e ∈ S, e.tail = u ∧ e.head = v) := by
  constructor
  · rintro ⟨e, he, ht, hh⟩
    change e.tail = u at ht
    change e.head = v at hh
    change e ∈ fullSelection (completeChainState n S) at he
    rw [completeChainState_fullSelection] at he
    rcases Finset.mem_union.mp he with he | he
    · rcases (mem_completeChainEdges n e).mp he with ⟨htop, htop'⟩ | ⟨hpos, hadj⟩
      · left
        exact ⟨ht.symm.trans htop, hh.symm.trans htop'⟩
      · right
        left
        simpa only [ht, hh] using And.intro hpos hadj
    · right
      right
      exact ⟨e, he, ht, hh⟩
  · rintro (⟨hu, hv⟩ | ⟨hpos, hadj⟩ | ⟨e, he, ht, hh⟩)
    · let e := completeCornerEdge n hn
      have he' : e ∈ fullSelection (completeChainState n S) := by
        rw [completeChainState_fullSelection]
        apply Finset.mem_union_left
        exact (mem_completeChainEdges n e).mpr (Or.inl
          ⟨completeCornerEdge_tail n hn, completeCornerEdge_head n hn⟩)
      subst u
      subst v
      exact ⟨e, he', completeCornerEdge_tail n hn, completeCornerEdge_head n hn⟩
    · exact completeChainState_chain S u v hpos hadj
    · have he' : e ∈ fullSelection (completeChainState n S) := by
        rw [completeChainState_fullSelection]
        exact Finset.mem_union_right _ he
      exact ⟨e, he', ht, hh⟩

/-- The additional-edge clause for a singleton state is a single endpoint test. -/
theorem completeChainState_selected_singleton_iff {n : ℕ} (hn : 0 < n)
    (e : Edge (completeDiagram n).area) (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (completeChainState n {e}).val u v ↔
      (u = 0 ∧ v = Fin.last n) ∨
        (0 < u.val ∧ u.val + 1 = v.val) ∨
        (e.tail = u ∧ e.head = v) := by
  simpa using
    (completeChainState_selected_iff hn ({e} : Finset (Edge (completeDiagram n).area)) u v)

end

end VerticalStripLLT.Circular.DiagramProof

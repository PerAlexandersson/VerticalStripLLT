import VerticalStripLLT.Components.DiagramProof.TerminalGraph
import VerticalStripLLT.Components.DiagramProof.TerminalPacking

/-! The terminal graph of a packed anchor is its support minus the receiver. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- Deleting the receiver before deleting the donor has no effect once the
receiver is inserted again. -/
theorem deleteEdges_deleteEdges_sup_edge {V : Type*} (H : SimpleGraph V)
    (e : Sym2 V) (c d : V) :
    (H.deleteEdges {s(c, d)}).deleteEdges {e} ⊔ SimpleGraph.edge c d =
      H.deleteEdges {e} ⊔ SimpleGraph.edge c d := by
  ext x y
  constructor
  · rintro (h | h)
    · rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
      rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
      exact Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨h.1.1, h.2⟩)
    · exact Or.inr h
  · rintro (h | h)
    · rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
      by_cases hpair : s(x, y) = s(c, d)
      · apply Or.inr
        rw [SimpleGraph.edge_adj]
        exact ⟨Sym2.eq_iff.mp hpair, h.1.ne⟩
      · apply Or.inl
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
          SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
        exact ⟨⟨h.1, hpair⟩, h.2⟩
    · exact Or.inr h

end VerticalStripLLT.Circular.DiagramProof

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- When every terminal pair has a natural copy, these copies test every
adjacency of a graph on the chains. -/
theorem graph_eq_of_terminal_copies (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧ F.terminal hforward v ≤ c.head)
    (G H : SimpleGraph {t : Fin n // F.terminal hforward t = t})
    (hcopies : ∀ p ∈ F.terminalEdges hforward,
      G.Adj (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔
      H.Adj (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head)) : G = H := by
  have hordered (B C : {t : Fin n // F.terminal hforward t = t})
      (hBC : B.val < C.val) : G.Adj B C ↔ H.Adj B C := by
    obtain ⟨p, hp, ht, hh⟩ := F.exists_terminalEdge_of_last_clique hforward c hterm
      B.val C.val (by simpa only [B.property, C.property] using hBC)
    have hB : F.chainVertex hforward p.tail = B := by
      apply Subtype.ext
      change F.terminal hforward p.tail = B.val
      rw [ht, F.terminal_idempotent, B.property]
    have hC : F.chainVertex hforward p.head = C := by
      apply Subtype.ext
      change F.terminal hforward p.head = C.val
      rw [hh, F.terminal_idempotent, C.property]
    simpa only [hB, hC] using hcopies p hp
  ext B C
  rcases lt_trichotomy B.val C.val with h | h | h
  · exact hordered B C h
  · have hBC : B = C := Subtype.ext h
    subst C
    simp
  · exact (G.adj_comm B C).trans ((hordered C B h).trans (H.adj_comm C B))

/-- Packing exactly the occupied terminal copies other than `f` produces
the original quotient with the receiver pair deleted. -/
theorem packed_terminal_graph_eq (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧ F.terminal hforward v ≤ c.head)
    (θ : Orientation D) (hθ : F.Anchor hforward θ) (η : Orientation D)
    (f : Edge D.area) (hf : f ∈ F.terminalEdges hforward)
    (hpacked : ∀ p ∈ F.terminalEdges hforward, p ∈ fullSelection η ↔
      0 < F.occupancy hforward θ (F.copyLabel hforward p) ∧ p ≠ f) :
    F.chainQuotient hforward (fullSelection η ∩ F.terminalEdges hforward) =
      (F.chainQuotient hforward (fullSelection θ)).deleteEdges
        {s(F.chainVertex hforward f.tail, F.chainVertex hforward f.head)} := by
  classical
  apply F.graph_eq_of_terminal_copies hforward c hterm
  intro p hp
  rw [F.chainQuotient_terminalEdges_adj_iff hforward _ Finset.inter_subset_right p hp]
  rw [Finset.mem_inter, and_iff_left hp, hpacked p hp]
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    F.terminal_pair_eq_iff hforward hp hf]
  obtain ⟨ht, hh⟩ := (F.mem_terminalEdges hforward p).mp hp
  have hlt : (F.chainVertex hforward p.tail).val <
      (F.chainVertex hforward p.head).val := by
    simpa only [chainVertex, ht, hh] using hforward p
  rw [F.chainQuotient_adj_iff_occupancy hforward θ hθ _ _ hlt]
  rfl

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

import VerticalStripLLT.Components.DiagramProof.PackedTerminalGraph

/-! The quotient support after moving one selected copy between terminal pairs. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical
open SimpleGraph

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Updating one occupancy removes the donor pair exactly when its old occupancy was one,
and adds the receiver pair. -/
theorem chainQuotient_of_occupancy_transfer (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧ F.terminal hforward v ≤ c.head)
    (θ η : Orientation D) (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η)
    (e f : Edge D.area) (he : e ∈ F.terminalEdges hforward)
    (hf : f ∈ F.terminalEdges hforward) (hef : e ≠ f)
    (hpositive : 0 < F.occupancy hforward θ (F.copyLabel hforward e))
    (hupdate : ∀ p, F.occupancy hforward η p =
      if p = F.copyLabel hforward e then F.occupancy hforward θ p - 1 else
        if p = F.copyLabel hforward f then F.occupancy hforward θ p + 1 else
          F.occupancy hforward θ p) :
    F.chainQuotient hforward (fullSelection η) =
      (if 1 < F.occupancy hforward θ (F.copyLabel hforward e) then
        F.chainQuotient hforward (fullSelection θ) else
        (F.chainQuotient hforward (fullSelection θ)).deleteEdges
          {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}) ⊔
      SimpleGraph.edge (F.chainVertex hforward f.tail) (F.chainVertex hforward f.head) := by
  apply F.graph_eq_of_terminal_copies hforward c hterm
  intro p hp
  obtain ⟨hpt, hph⟩ := (F.mem_terminalEdges hforward p).mp hp
  have hlt : (F.chainVertex hforward p.tail).val <
      (F.chainVertex hforward p.head).val := by
    simpa only [chainVertex, hpt, hph] using hforward p
  have hleft := F.chainQuotient_adj_iff_occupancy hforward η hη
    (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) hlt
  have hbase := F.chainQuotient_adj_iff_occupancy hforward θ hθ
    (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) hlt
  change (F.chainQuotient hforward (fullSelection η)).Adj
    (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔
      0 < F.occupancy hforward η (F.copyLabel hforward p) at hleft
  change (F.chainQuotient hforward (fullSelection θ)).Adj
    (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔
      0 < F.occupancy hforward θ (F.copyLabel hforward p) at hbase
  have hdelete :
      ((F.chainQuotient hforward (fullSelection θ)).deleteEdges
        {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}).Adj
          (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔
        0 < F.occupancy hforward θ (F.copyLabel hforward p) ∧ p ≠ e := by
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
      F.terminal_pair_eq_iff hforward hp he, hbase]
  have hne : F.chainVertex hforward p.tail ≠ F.chainVertex hforward p.head :=
    fun h => hlt.ne (congrArg Subtype.val h)
  have hreceiver :
      (SimpleGraph.edge (F.chainVertex hforward f.tail) (F.chainVertex hforward f.head)).Adj
          (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔ p = f := by
    rw [SimpleGraph.edge_adj, ← Sym2.eq_iff,
      F.terminal_pair_eq_iff hforward hp hf, and_iff_left hne]
  rw [hleft, SimpleGraph.sup_adj, hreceiver]
  have hlabel (q : Edge D.area) (hq : q ∈ F.terminalEdges hforward) :
      F.copyLabel hforward p = F.copyLabel hforward q ↔ p = q :=
    ⟨F.terminalEdges_label_injective hforward hp hq, fun h => congrArg _ h⟩
  simp only [hupdate, hlabel e he, hlabel f hf]
  by_cases hcount : 1 < F.occupancy hforward θ (F.copyLabel hforward e)
  · rw [ite_eq_left hcount, hbase]
    by_cases hpe : p = e
    · subst p
      simp only [ite_true, hef]
      lia
    · by_cases hpf : p = f
      · subst p
        simp [hpe]
      · simp [hpe, hpf]
  · rw [ite_eq_right hcount, hdelete]
    by_cases hpe : p = e
    · subst p
      simp only [ite_true, ne_eq, not_true_eq_false, and_false, hef, false_or]
      lia
    · by_cases hpf : p = f
      · subst p
        simp [hpe]
      · simp [hpe, hpf]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

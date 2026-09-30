import VerticalStripLLT.Components.DiagramProof.TerminalClique
import VerticalStripLLT.Components.DiagramProof.QuotientOccupancy

/-! Capacity and missing-edge interfaces for the terminal clique. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Every distinct pair of terminal chains has its terminal copy in the last clique. -/
theorem exists_terminalEdge_of_pair (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧
      F.terminal hforward v ≤ c.head)
    (B C : {t : Fin n // F.terminal hforward t = t}) (hBC : B ≠ C) :
    ∃ p ∈ F.terminalEdges hforward,
      s(F.chainVertex hforward p.tail, F.chainVertex hforward p.head) = s(B, C) := by
  have hval : B.val ≠ C.val := by
    intro h
    exact hBC (Subtype.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · obtain ⟨p, hp, ht, hh⟩ := F.exists_terminalEdge_of_last_clique hforward c hterm
      B.val C.val (by simpa only [B.property, C.property] using hlt)
    have hB : F.chainVertex hforward p.tail = B := by
      apply Subtype.ext
      change F.terminal hforward p.tail = B.val
      rw [ht, F.terminal_idempotent, B.property]
    have hC : F.chainVertex hforward p.head = C := by
      apply Subtype.ext
      change F.terminal hforward p.head = C.val
      rw [hh, F.terminal_idempotent, C.property]
    exact ⟨p, hp, Sym2.eq_iff.mpr (Or.inl ⟨hB, hC⟩)⟩
  · obtain ⟨p, hp, ht, hh⟩ := F.exists_terminalEdge_of_last_clique hforward c hterm
      C.val B.val (by simpa only [B.property, C.property] using hgt)
    have hC : F.chainVertex hforward p.tail = C := by
      apply Subtype.ext
      change F.terminal hforward p.tail = C.val
      rw [ht, F.terminal_idempotent, C.property]
    have hB : F.chainVertex hforward p.head = B := by
      apply Subtype.ext
      change F.terminal hforward p.head = B.val
      rw [hh, F.terminal_idempotent, B.property]
    exact ⟨p, hp, Sym2.eq_iff.mpr (Or.inr ⟨hC, hB⟩)⟩

/-- The simple graph edge associated to a terminal-copy pair agrees with the
corresponding edge between the abstract terminal vertices. -/
theorem simpleGraph_edge_eq_of_terminal_pair
    {B C : {t : Fin n // F.terminal hforward t = t}}
    {p : Edge D.area}
    (hpair : s(F.chainVertex hforward p.tail, F.chainVertex hforward p.head) = s(B, C)) :
    SimpleGraph.edge (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) =
      SimpleGraph.edge B C := by
  unfold SimpleGraph.edge
  rw [hpair]

/-- Every terminal-copy label has positive capacity among good edges. -/
theorem terminal_capacity_pos {p : Edge D.area}
    (hp : p ∈ F.terminalEdges hforward) :
    0 < ((F.goodEdges hforward).filter
      (fun g => F.copyLabel hforward g = F.copyLabel hforward p)).card := by
  apply Finset.card_pos.mpr
  refine ⟨p, Finset.mem_filter.mpr ⟨?_, rfl⟩⟩
  exact (F.terminalEdge_good_not_corner hforward hp).1

/-- An absent terminal quotient edge has zero occupancy at its terminal label. -/
theorem occupancy_eq_zero_of_not_adj (θ : Orientation D) (hθ : F.Anchor hforward θ)
    {p : Edge D.area} (hp : p ∈ F.terminalEdges hforward)
    (hnot : ¬ (F.chainQuotient hforward (fullSelection θ)).Adj
      (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head)) :
    F.occupancy hforward θ (F.copyLabel hforward p) = 0 := by
  obtain ⟨ht, hh⟩ := (F.mem_terminalEdges hforward p).mp hp
  have hlt : (F.chainVertex hforward p.tail).val <
      (F.chainVertex hforward p.head).val := by
    simpa only [chainVertex, ht, hh] using hforward p
  have hzero : ¬ 0 < F.occupancy hforward θ
      ((F.chainVertex hforward p.tail).val,
        (F.chainVertex hforward p.head).val) := by
    intro hpos
    exact hnot ((F.chainQuotient_adj_iff_occupancy hforward θ hθ _ _ hlt).mpr hpos)
  have hz := Nat.eq_zero_of_not_pos hzero
  simpa only [copyLabel, chainVertex, ht, hh] using hz

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

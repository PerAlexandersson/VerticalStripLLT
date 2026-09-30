import VerticalStripLLT.Components.DiagramProof.ChainQuotient
import VerticalStripLLT.Components.DiagramProof.ParallelPacking
import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! Quotient adjacencies read directly from selected copy occupancies. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- For an anchor, increasing quotient adjacency is exactly positive occupancy. -/
theorem chainQuotient_adj_iff_occupancy (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (B C : {t : Fin n // F.terminal hforward t = t}) (hBC : B.val < C.val) :
    (F.chainQuotient hforward (fullSelection θ)).Adj B C ↔
      0 < F.occupancy hforward θ (B.val, C.val) := by
  constructor
  · rintro ⟨_, h | h⟩
    · obtain ⟨e, he, ht, hh⟩ := h
      rw [occupancy]
      apply Finset.card_pos.mpr
      refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
      change (F.terminal hforward e.tail, F.terminal hforward e.head) = (B.val, C.val)
      exact Prod.ext ht hh
    · obtain ⟨e, he, ht, hh⟩ := h
      have hle := F.selected_terminal_le hforward hθ.2
        ((mem_fullSelection_iff_selected θ e).mp he)
      rw [ht, hh] at hle
      exact ((not_le_of_gt hBC) hle).elim
  · intro h
    rw [occupancy] at h
    obtain ⟨e, he⟩ := Finset.card_pos.mp h
    obtain ⟨hefull, hlabel⟩ := Finset.mem_filter.mp he
    have hlabel' : (F.terminal hforward e.tail, F.terminal hforward e.head) =
        (B.val, C.val) := by
      simpa only [copyLabel] using hlabel
    refine ⟨fun h => hBC.ne (congrArg Subtype.val h), Or.inl ⟨e, hefull, ?_, ?_⟩⟩
    · exact congrArg Prod.fst hlabel'
    · exact congrArg Prod.snd hlabel'

/-- A terminal copy represents precisely its quotient adjacency among terminal-only edges. -/
theorem chainQuotient_terminalEdges_adj_iff (A : Finset (Edge D.area))
    (hA : A ⊆ F.terminalEdges hforward) (p : Edge D.area)
    (hp : p ∈ F.terminalEdges hforward) :
    (F.chainQuotient hforward A).Adj
        (F.chainVertex hforward p.tail) (F.chainVertex hforward p.head) ↔
      p ∈ A := by
  obtain ⟨hpt, hph⟩ := (F.mem_terminalEdges hforward p).mp hp
  have hlt : p.tail < p.head := hforward p
  constructor
  · rintro ⟨_, h | h⟩
    · obtain ⟨e, he, ht, hh⟩ := h
      have heterminal := (F.mem_terminalEdges hforward e).mp (hA he)
      have hetail : e.tail = p.tail := by
        calc
          e.tail = F.terminal hforward e.tail := heterminal.1.symm
          _ = (F.chainVertex hforward p.tail).val := ht
          _ = F.terminal hforward p.tail := rfl
          _ = p.tail := hpt
      have hehead : e.head = p.head := by
        calc
          e.head = F.terminal hforward e.head := heterminal.2.symm
          _ = (F.chainVertex hforward p.head).val := hh
          _ = F.terminal hforward p.head := rfl
          _ = p.head := hph
      have hep : e = p := D.endpointEmbedding.injective (Prod.ext hetail hehead)
      exact hep ▸ he
    · obtain ⟨e, he, ht, hh⟩ := h
      have heterminal := (F.mem_terminalEdges hforward e).mp (hA he)
      have hetail : e.tail = p.head := by
        calc
          e.tail = F.terminal hforward e.tail := heterminal.1.symm
          _ = (F.chainVertex hforward p.head).val := ht
          _ = F.terminal hforward p.head := rfl
          _ = p.head := hph
      have hehead : e.head = p.tail := by
        calc
          e.head = F.terminal hforward e.head := heterminal.2.symm
          _ = (F.chainVertex hforward p.tail).val := hh
          _ = F.terminal hforward p.tail := rfl
          _ = p.tail := hpt
      have hforwarde := hforward e
      rw [hetail, hehead] at hforwarde
      exact ((not_lt_of_ge hlt.le) hforwarde).elim
  · intro hpA
    have hne : F.chainVertex hforward p.tail ≠ F.chainVertex hforward p.head := by
      intro h
      have hval := congrArg Subtype.val h
      exact hlt.ne (by simpa only [chainVertex, hpt, hph] using hval)
    refine ⟨hne, Or.inl ⟨p, hpA, ?_, ?_⟩⟩
    · simp only [chainVertex, hpt]
    · simp only [chainVertex, hph]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

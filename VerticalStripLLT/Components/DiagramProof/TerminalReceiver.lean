import VerticalStripLLT.Components.DiagramProof.ConnectedExchange
import VerticalStripLLT.Components.DiagramProof.TerminalCapacity

/-! A connected terminal receiver for a positive occupancy transfer. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- A terminal occupancy deficit can be chosen so that moving one donor copy to it
preserves connected quotient support. -/
theorem exists_terminal_receiver (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧ F.terminal hforward v ≤ c.head)
    (θ τ : Orientation D) (hθ : F.Anchor hforward θ) (hτ : F.Anchor hforward τ)
    (hH : (F.chainQuotient hforward (fullSelection θ)).Connected)
    (hJ : (F.chainQuotient hforward (fullSelection τ)).Connected)
    (e : Edge D.area) (he : e ∈ F.terminalEdges hforward)
    (hdonor : F.occupancy hforward τ (F.copyLabel hforward e) <
      F.occupancy hforward θ (F.copyLabel hforward e))
    (f₀ : Edge D.area) (hf₀ : f₀ ∈ F.terminalEdges hforward)
    (hdeficit : F.occupancy hforward θ (F.copyLabel hforward f₀) <
      F.occupancy hforward τ (F.copyLabel hforward f₀)) :
    ∃ f ∈ F.terminalEdges hforward,
      F.occupancy hforward θ (F.copyLabel hforward f) <
        F.occupancy hforward τ (F.copyLabel hforward f) ∧
      e ≠ f ∧
      ((if 1 < F.occupancy hforward θ (F.copyLabel hforward e) then
        F.chainQuotient hforward (fullSelection θ)
      else
        (F.chainQuotient hforward (fullSelection θ)).deleteEdges
          {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}) ⊔
        SimpleGraph.edge (F.chainVertex hforward f.tail)
          (F.chainVertex hforward f.head)).Connected := by
  let H := F.chainQuotient hforward (fullSelection θ)
  let J := F.chainQuotient hforward (fullSelection τ)
  change H.Connected at hH
  change J.Connected at hJ
  change ∃ f ∈ F.terminalEdges hforward,
    F.occupancy hforward θ (F.copyLabel hforward f) <
        F.occupancy hforward τ (F.copyLabel hforward f) ∧
      e ≠ f ∧
      ((if 1 < F.occupancy hforward θ (F.copyLabel hforward e) then H else
        H.deleteEdges {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}) ⊔
        SimpleGraph.edge (F.chainVertex hforward f.tail)
          (F.chainVertex hforward f.head)).Connected
  obtain ⟨het, heh⟩ := (F.mem_terminalEdges hforward e).mp he
  have he_lt : (F.chainVertex hforward e.tail).val <
      (F.chainVertex hforward e.head).val := by
    simpa only [chainVertex, het, heh] using hforward e
  have he_pos : 0 < F.occupancy hforward θ (F.copyLabel hforward e) := by
    lia
  have he_adj : H.Adj (F.chainVertex hforward e.tail)
      (F.chainVertex hforward e.head) := by
    apply (F.chainQuotient_adj_iff_occupancy hforward θ hθ _ _ he_lt).mpr
    exact he_pos
  have he_edge : s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head) ∈
      H.edgeSet := H.mem_edgeSet.mpr he_adj
  by_cases hmany : 1 < F.occupancy hforward θ (F.copyLabel hforward e)
  · refine ⟨f₀, hf₀, hdeficit, ?_, ?_⟩
    · intro hef
      subst f₀
      lia
    · simp only [ite_eq_left hmany]
      exact hH.mono le_sup_left
  · have he_one : F.occupancy hforward θ (F.copyLabel hforward e) = 1 := by
      lia
    have he_zero : F.occupancy hforward τ (F.copyLabel hforward e) = 0 := by
      lia
    have he_not_J : s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head) ∉
        J.edgeSet := by
      intro heJ
      have heJ_adj : J.Adj (F.chainVertex hforward e.tail)
          (F.chainVertex hforward e.head) := J.mem_edgeSet.mp heJ
      have heJ_pos : 0 < F.occupancy hforward τ (F.copyLabel hforward e) :=
        (F.chainQuotient_adj_iff_occupancy hforward τ hτ _ _ he_lt).mp heJ_adj
      lia
    by_cases hbridge : H.IsBridge
        s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)
    · rcases VerticalStripLLT.Circular.DiagramProof.SimpleGraph.exists_reconnecting_edge H J
        (F.chainVertex hforward e.tail) (F.chainVertex hforward e.head) hH hJ hbridge he_not_J
        with ⟨g, ⟨hgJ, hgH⟩, hconnected⟩
      revert hgJ hgH hconnected
      refine Sym2.inductionOn g ?_
      intro B C hconnected hgJ hgH
      have hJ_adj : J.Adj B C := J.mem_edgeSet.mp hgJ
      have hBC : B ≠ C := hJ_adj.ne
      obtain ⟨f, hf, hpair⟩ := F.exists_terminalEdge_of_pair hforward c hterm B C hBC
      have hfJ_adj : J.Adj (F.chainVertex hforward f.tail)
          (F.chainVertex hforward f.head) := by
        apply J.mem_edgeSet.mp
        rw [hpair]
        exact hgJ
      have hf_lt : (F.chainVertex hforward f.tail).val <
          (F.chainVertex hforward f.head).val := by
        obtain ⟨hft, hfh⟩ := (F.mem_terminalEdges hforward f).mp hf
        simpa only [chainVertex, hft, hfh] using hforward f
      have hf_pos : 0 < F.occupancy hforward τ (F.copyLabel hforward f) :=
        (F.chainQuotient_adj_iff_occupancy hforward τ hτ _ _ hf_lt).mp hfJ_adj
      have hf_not_H : ¬ H.Adj (F.chainVertex hforward f.tail)
          (F.chainVertex hforward f.head) := by
        intro hfH
        apply hgH
        rw [← hpair]
        exact H.mem_edgeSet.mpr hfH
      have hf_zero := F.occupancy_eq_zero_of_not_adj hforward θ hθ hf hf_not_H
      refine ⟨f, hf, ?_, ?_, ?_⟩
      · rw [hf_zero]
        exact hf_pos
      · intro hef
        subst f
        apply hgH
        rw [← hpair]
        exact he_edge
      · simp only [ite_eq_right hmany]
        simpa only [SimpleGraph.edge, hpair] using hconnected
    · have hdelete : (H.deleteEdges
          {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}).Connected :=
        hH.preconnected.connected_deleteEdges_of_not_isBridge hbridge
      refine ⟨f₀, hf₀, hdeficit, ?_, ?_⟩
      · intro hef
        subst f₀
        lia
      · simp only [ite_eq_right hmany]
        exact hdelete.mono le_sup_left

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

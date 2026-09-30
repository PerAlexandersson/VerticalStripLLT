import VerticalStripLLT.Components.DiagramProof.TerminalTransfer
import VerticalStripLLT.Components.DiagramProof.TerminalRepair
import VerticalStripLLT.Components.DiagramProof.TerminalCapacity
import VerticalStripLLT.Components.DiagramProof.OccupancySupport

/-! Every support-preserving terminal transfer is an actual flip path. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- A positive donor can transfer one unit to a vacant receiver whenever the
resulting support is connected. One absent terminal pair repairs either obstruction. -/
theorem exists_terminal_transfer (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ : Orientation D) (hθ : F.Anchor hforward θ) (e f : Edge D.area)
    (heT : e ∈ F.terminalEdges hforward) (hfT : f ∈ F.terminalEdges hforward)
    (hef : e ≠ f) (he : 0 < F.occupancy hforward θ (F.copyLabel hforward e))
    (hf : F.occupancy hforward θ (F.copyLabel hforward f) <
      ((F.goodEdges hforward).filter
        (fun g => F.copyLabel hforward g = F.copyLabel hforward f)).card)
    (hconnected : (F.chainQuotient hforward (fullSelection θ)).Connected)
    (hfinal : ((if 1 < F.occupancy hforward θ (F.copyLabel hforward e)
      then F.chainQuotient hforward (fullSelection θ)
      else (F.chainQuotient hforward (fullSelection θ)).deleteEdges
        {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)}) ⊔
      SimpleGraph.edge (F.chainVertex hforward f.tail)
        (F.chainVertex hforward f.head)).Connected) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      ∀ p, F.occupancy hforward η p =
        if p = F.copyLabel hforward e then F.occupancy hforward θ p - 1
        else if p = F.copyLabel hforward f then F.occupancy hforward θ p + 1
        else F.occupancy hforward θ p := by
  classical
  let H := F.chainQuotient hforward (fullSelection θ)
  have terminal_ne (p : Edge D.area) (hp : p ∈ F.terminalEdges hforward) :
      F.chainVertex hforward p.tail ≠ F.chainVertex hforward p.head := by
    obtain ⟨ht, hh⟩ := (F.mem_terminalEdges hforward p).mp hp
    intro h
    exact (hforward p).ne (by
      simpa only [chainVertex, ht, hh] using congrArg Subtype.val h)
  have heAdj : H.Adj (F.chainVertex hforward e.tail) (F.chainVertex hforward e.head) := by
    obtain ⟨ht, hh⟩ := (F.mem_terminalEdges hforward e).mp heT
    have hlt : (F.chainVertex hforward e.tail).val <
        (F.chainVertex hforward e.head).val := by
      simpa only [chainVertex, ht, hh] using hforward e
    have hiff := F.chainQuotient_adj_iff_occupancy hforward θ hθ
      (F.chainVertex hforward e.tail) (F.chainVertex hforward e.head) hlt
    change H.Adj _ _ ↔ 0 < F.occupancy hforward θ (F.copyLabel hforward e) at hiff
    exact hiff.mpr he
  have hefpair : s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head) ≠
      s(F.chainVertex hforward f.tail, F.chainVertex hforward f.head) :=
    fun h => hef ((F.terminal_pair_eq_iff hforward heT hfT).mp h)
  have hrepair := TerminalRepair.one_temporary_edge_repair H hconnected
    (F.chainVertex hforward e.tail) (F.chainVertex hforward e.head)
    (F.chainVertex hforward f.tail) (F.chainVertex hforward f.head)
    heAdj (terminal_ne f hfT) hefpair
    (decide (1 < F.occupancy hforward θ (F.copyLabel hforward e)))
    (by simpa [H] using hfinal)
  rcases hrepair with ⟨h₁, h₂⟩ | ⟨x, y, hxy, habsent, hge, hgf, h₁, h₂, h₃, h₄⟩
  · exact F.exists_direct_terminal_transfer hforward c hc hlast hterm θ hθ e f
      heT hfT hef he hf h₁.preconnected h₂.preconnected
  · obtain ⟨g, hgT, hpair⟩ := F.exists_terminalEdge_of_pair hforward c
      (fun v => ⟨hterm v, hlast _⟩) x y hxy
    have hedge : SimpleGraph.edge (F.chainVertex hforward g.tail)
        (F.chainVertex hforward g.head) = SimpleGraph.edge x y := by
      unfold SimpleGraph.edge
      rw [hpair]
    have hge' : g ≠ e := by
      intro h
      subst g
      exact hge hpair.symm
    have hgf' : g ≠ f := by
      intro h
      subst g
      exact hgf hpair.symm
    have habsent' : ¬H.Adj (F.chainVertex hforward g.tail)
        (F.chainVertex hforward g.head) := by
      intro h
      apply habsent
      apply H.mem_edgeSet.mp
      rw [← hpair]
      exact H.mem_edgeSet.mpr h
    have hzero := F.occupancy_eq_zero_of_not_adj hforward θ hθ hgT habsent'
    have hcapacity := F.terminal_capacity_pos hforward hgT
    have hvac : F.occupancy hforward θ (F.copyLabel hforward g) <
        ((F.goodEdges hforward).filter
          (fun p => F.copyLabel hforward p = F.copyLabel hforward g)).card := by
      rw [hzero]
      exact hcapacity
    obtain ⟨σ, hθσ, hσ, hfirst⟩ := F.exists_direct_terminal_transfer hforward c hc hlast
      hterm θ hθ e g heT hgT hge'.symm he hvac
      (by simpa only [hpair] using h₁.preconnected)
      (by simpa only [hedge] using h₂.preconnected)
    have hsupport := F.chainQuotient_of_occupancy_transfer hforward c
      (fun v => ⟨hterm v, hlast _⟩) θ σ hθ hσ e g heT hgT hge'.symm he hfirst
    rw [hedge] at hsupport
    have hleg : F.copyLabel hforward e ≠ F.copyLabel hforward g := fun h =>
      hge' (F.terminalEdges_label_injective hforward heT hgT h).symm
    have hlgf : F.copyLabel hforward g ≠ F.copyLabel hforward f := fun h =>
      hgf' (F.terminalEdges_label_injective hforward hgT hfT h)
    have hlef : F.copyLabel hforward e ≠ F.copyLabel hforward f := fun h =>
      hef (F.terminalEdges_label_injective hforward heT hfT h)
    have hgσ : 0 < F.occupancy hforward σ (F.copyLabel hforward g) := by
      simp [hfirst, hleg.symm]
    have hfσ : F.occupancy hforward σ (F.copyLabel hforward f) <
        ((F.goodEdges hforward).filter
          (fun p => F.copyLabel hforward p = F.copyLabel hforward f)).card := by
      simpa only [hfirst, ite_eq_right hlef.symm, ite_eq_right hlgf.symm] using hf
    obtain ⟨η, hση, hη, hsecond⟩ := F.exists_direct_terminal_transfer hforward c hc hlast
      hterm σ hσ g f hgT hfT hgf' hgσ hfσ
      (by simpa only [hsupport, decide_eq_true_eq] using h₃.preconnected)
      (by simpa only [hsupport, hpair, decide_eq_true_eq] using h₄.preconnected)
    refine ⟨η, hθσ.trans hση, hη, ?_⟩
    intro p
    simp only [hsecond, hfirst]
    by_cases hpe : p = F.copyLabel hforward e
    · subst p
      simp [hleg, hlef]
    · by_cases hpf : p = F.copyLabel hforward f
      · subst p
        simp [hlef.symm, hlgf.symm]
      · by_cases hpg : p = F.copyLabel hforward g
        · subst p
          simp [hleg.symm, hlgf]
        · simp [hpe, hpf, hpg]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

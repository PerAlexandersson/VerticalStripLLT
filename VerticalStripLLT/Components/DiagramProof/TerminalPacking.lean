import VerticalStripLLT.Components.DiagramProof.TerminalClique
import VerticalStripLLT.Components.DiagramProof.RepresentativePacking

/-! Packing occupied chain pairs at their terminal copies by actual flips. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Pack one terminal copy of every occupied pair, except the receiver pair.
The counts of all pairs are preserved, and the returned anchor is reached by flips. -/
theorem exists_terminal_packing (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (f : Edge D.area) (hf : f ∈ F.terminalEdges hforward)
    (hvac : F.occupancy hforward θ (F.copyLabel hforward f) <
      ((F.goodEdges hforward).filter
        (fun e => F.copyLabel hforward e = F.copyLabel hforward f)).card) :
    ∃ η : Orientation D, F.Anchor hforward η ∧
      Relation.ReflTransGen (Flip D) θ η ∧
      (∀ p, F.occupancy hforward η p = F.occupancy hforward θ p) ∧
      (∀ p ∈ F.terminalEdges hforward, p ∈ fullSelection η ↔
        0 < F.occupancy hforward θ (F.copyLabel hforward p) ∧ p ≠ f) := by
  classical
  have hsub := (F.anchor_iff_subsets hforward θ).mp hθ
  obtain ⟨T, hCT, hTG, hcounts, hterminal⟩ := exists_representative_packing
    (fullSelection θ) (F.goodEdges hforward) F.edges (F.terminalEdges hforward)
    (F.copyLabel hforward) f hsub.2 hsub.1
    (fun _ hp => (F.terminalEdge_good_not_corner hforward hp).1)
    (fun _ _ hp hq heq => F.terminalEdges_label_injective hforward hp hq heq)
    (fun _ hc _ hp => F.corner_label_ne_terminalEdge hforward hc hp) hf
    (by
      convert hvac using 1 <;> congr 1 <;> ext x <;> simp)
  let η := ofFullSelection hforward T (F.contains_strict.trans hCT)
  have hη : F.Anchor hforward η := F.anchor_ofFullSelection hforward T hCT hTG
  have hfull : fullSelection η = T := fullSelection_ofFullSelection hforward T _
  have hocc : ∀ p, F.occupancy hforward η p = F.occupancy hforward θ p := by
    intro p
    unfold occupancy
    rw [hfull]
    convert hcounts p using 1 <;> congr 1 <;> ext x <;> simp
  refine ⟨η, hη, F.anchors_connected_of_occupancy hforward hθ hη
    (fun p => (hocc p).symm), hocc, ?_⟩
  intro p hp
  rw [hfull]
  unfold occupancy
  convert hterminal p hp using 3
  congr 1
  ext x
  simp

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

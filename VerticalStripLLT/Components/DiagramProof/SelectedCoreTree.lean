import VerticalStripLLT.Components.DiagramProof.AnchorSizes
import VerticalStripLLT.Components.DiagramProof.InducedRestriction

/-! A selected ambient realization of a core tree makes the core connected. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {E : Diagram (k + 1)} {D : Diagram n}

/-- A connected core graph whose natural edges are selected after embedding gives a
connected induced restriction. -/
theorem selectedConnected_inducedRestrict_of_selected_tree (hE : Forward E)
    (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ u v,
      (∃ e : Edge E.area, e.tail = u ∧ e.head = v) ↔
        ∃ f : Edge D.area, f.tail = ι u ∧ f.head = ι v)
    (hstrict : ∀ u v,
      (∃ e ∈ E.strict, e.tail = u ∧ e.head = v) ↔
        ∃ f ∈ D.strict, f.tail = ι u ∧ f.head = ι v)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.Connected)
    (hTG : T ≤ edgeSetGraph (Finset.univ : Finset (Edge E.area)))
    (θ : Orientation D)
    (hselected : ∀ e : Edge E.area, T.Adj e.tail e.head →
      D.edgeData.selected θ.val (ι e.tail) (ι e.head)) :
    SelectedConnected (inducedRestrict hE ι hnatural hstrict θ) := by
  let α := inducedRestrict hE ι hnatural hstrict θ
  have hsub : T ≤ edgeSetGraph (fullSelection α) := by
    intro u v huv
    rcases hTG huv with ⟨_, h | h⟩
    · rcases h with ⟨e, _, ht, hh⟩
      have hTe : T.Adj e.tail e.head := by
        simpa only [ht, hh] using huv
      have hsel : E.edgeData.selected α.val e.tail e.head := by
        apply (inducedRestrict_selected hE ι hnatural hstrict θ e.tail e.head).mpr
        exact hselected e hTe
      have hedge : (edgeSetGraph (fullSelection α)).Adj e.tail e.head :=
        (edgeSetGraph_adj_iff_mem hE (fullSelection α) e).mpr
          ((mem_fullSelection_iff_selected α e).mpr hsel)
      simpa only [ht, hh] using hedge
    · rcases h with ⟨e, _, ht, hh⟩
      have hTe : T.Adj e.tail e.head := by
        simpa only [ht, hh] using huv.symm
      have hsel : E.edgeData.selected α.val e.tail e.head := by
        apply (inducedRestrict_selected hE ι hnatural hstrict θ e.tail e.head).mpr
        exact hselected e hTe
      have hedge : (edgeSetGraph (fullSelection α)).Adj e.tail e.head :=
        (edgeSetGraph_adj_iff_mem hE (fullSelection α) e).mpr
          ((mem_fullSelection_iff_selected α e).mpr hsel)
      simpa only [ht, hh] using hedge.symm
  apply (edgeSetGraph_fullSelection_preconnected_iff α).mp
  exact hT.preconnected.mono hsub

end

end VerticalStripLLT.Circular.DiagramProof

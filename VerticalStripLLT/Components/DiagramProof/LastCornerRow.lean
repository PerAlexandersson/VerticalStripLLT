import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! The selected row of a last retained corner in an anchor. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

theorem anchor_selected_from_last_tail_iff (θ : Orientation D)
    (hθ : F.Anchor hforward θ) (e : Edge D.area) (he : e ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ e.head) (v : Fin n) :
    D.edgeData.selected θ.val e.tail v ↔ v = e.head := by
  constructor
  · intro hv
    obtain ⟨f, hf, htail, hhead⟩ := hv
    have hgood : F.GoodEdge hforward f := hθ.2 f hf
    have hfe : f = e := F.goodEdge_eq_last_corner_of_tail hforward e he hlast
      hgood htail
    rw [hfe] at hhead
    exact hhead.symm
  · intro hv
    subst v
    apply (mem_fullSelection_iff_selected θ e).mp
    exact hθ.1 he

theorem anchor_not_selected_last_tail_of_lt (θ : Orientation D)
    (hθ : F.Anchor hforward θ) (e : Edge D.area) (he : e ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ e.head) {v : Fin n} (hv : v < e.head) :
    ¬ D.edgeData.selected θ.val e.tail v := by
  intro h
  exact hv.ne ((F.anchor_selected_from_last_tail_iff hforward θ hθ e he hlast v).mp h)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

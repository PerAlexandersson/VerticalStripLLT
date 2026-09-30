import VerticalStripLLT.Components.DiagramProof.LastCliqueCoreReplacement
import VerticalStripLLT.Components.DiagramProof.LastCornerRow

/-! Core replacement specialized to anchors at a last retained corner. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

theorem exists_lastClique_anchor_replacement
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hgc : g.tail < c) (hcg : c < g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (α : Orientation (inducedDiagram hD ι))
    (hα : (allCorners (inducedDiagram hD ι)).Anchor
      (inducedDiagram_forward hD ι) α)
    (hp : Relation.ReflTransGen (Flip (inducedDiagram hD ι))
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ) α) :
    ∃ ζ : Orientation D, Relation.ReflTransGen (Flip D) θ ζ ∧
      (∀ u v, D.edgeData.selected ζ.val (ι u) (ι v) ↔
        (inducedDiagram hD ι).edgeData.selected α.val u v) ∧
      (∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
        (D.edgeData.selected ζ.val u v ↔ D.edgeData.selected θ.val u v)) := by
  obtain ⟨i, hi⟩ := (himage g.tail).mpr (Or.inl hgc.le)
  obtain ⟨j, hj⟩ := (himage g.head).mpr (Or.inr rfl)
  have hac : ι i < c := by simpa only [hi] using hgc
  have hce : c < ι j := by simpa only [hj] using hcg
  obtain ⟨f, hfi, hfj⟩ :=
    (inducedDiagram_naturalEdge_iff hD ι i j).mpr ⟨g, hi.symm, hj.symm⟩
  have hef : inducedEdge hD ι f = g := by
    apply D.endpointEmbedding.injective
    apply Prod.ext
    · exact (inducedEdge_tail hD ι f).trans ((congrArg ι hfi).trans hi)
    · exact (inducedEdge_head hD ι f).trans ((congrArg ι hfj).trans hj)
  have hfcorner : IsCorner f := by
    apply isCorner_of_inducedEdge_isCorner hD ι f
    simpa only [hef] using (allCorners D).corner g (by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  have hfmem : f ∈ (allCorners (inducedDiagram hD ι)).edges := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfcorner⟩
  have hae : Cover θ g.tail g.head := by
    exact (allCorners D).commonCover_of_anchor hD hθ g
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  have hαcover : Cover α i j := by
    simpa only [hfi, hfj] using
      (allCorners (inducedDiagram hD ι)).commonCover_of_anchor
        (inducedDiagram_forward hD ι) hα f hfmem
  have hrow : ∀ v, ι i < v → v < ι j →
      ¬ D.edgeData.selected θ.val (ι i) v := by
    intro v _ hv
    simpa only [hi, hj] using
      ((allCorners D).anchor_not_selected_last_tail_of_lt hD θ hθ g
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩) hlast (hv.trans_eq hj))
  have hflast : ∀ v : Fin (k + 1), v ≤ f.head := by
    intro v
    apply ι.le_iff_le.mp
    rw [hfj, hj]
    exact hlast (ι v)
  have hαrow : ∀ v, ι v ≤ c →
      ¬ (inducedDiagram hD ι).edgeData.selected α.val i v := by
    intro v hvc hv
    have hvj : v < j := ι.lt_iff_lt.mp (hvc.trans_lt hce)
    have hrowf := (allCorners (inducedDiagram hD ι)).anchor_selected_from_last_tail_iff
      (inducedDiagram_forward hD ι) α hα f hfmem hflast v
    exact (hvj.ne ((hrowf.mp (by simpa only [hfi] using hv)).trans hfj)).elim
  exact exists_lastClique_core_replacement hD ι c i j hac hce
    (by simpa only [hj] using himage) θ (by simpa only [hi, hj] using hae) hrow α hαcover hαrow hp

end

end VerticalStripLLT.Circular.DiagramProof

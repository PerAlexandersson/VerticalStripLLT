import VerticalStripLLT.Components.DiagramProof.InducedDecorations
import VerticalStripLLT.Components.DiagramProof.LastCliqueLift
import VerticalStripLLT.Components.DiagramProof.LastCliqueSweep
import VerticalStripLLT.Components.DiagramProof.LastCliqueRestoration

/-! Sweep, replace the core along an actual path, and restore the original exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof

set_option backward.isDefEq.respectTransparency false

variable {k n : ℕ} {D : Diagram n}

/-- A core path between states with the required last-corner row lifts with the
original exterior restored. No cover condition is imposed on intermediate core states. -/
theorem exists_lastClique_core_replacement (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (c : Fin n) (i j : Fin (k + 1)) (hac : ι i < c) (hce : c < ι j)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = ι j)
    (θ : Orientation D) (hae : Cover θ (ι i) (ι j))
    (hrow : ∀ v, ι i < v → v < ι j → ¬ D.edgeData.selected θ.val (ι i) v)
    (α : Orientation (inducedDiagram hD ι)) (hαcover : Cover α i j)
    (hαrow : ∀ v, ι v ≤ c → ¬ (inducedDiagram hD ι).edgeData.selected α.val i v)
    (hp : Relation.ReflTransGen (Flip (inducedDiagram hD ι))
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ) α) :
    ∃ ζ : Orientation D, Relation.ReflTransGen (Flip D) θ ζ ∧
      (∀ u v, D.edgeData.selected ζ.val (ι u) (ι v) ↔
        (inducedDiagram hD ι).edgeData.selected α.val u v) ∧
      (∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
        (D.edgeData.selected ζ.val u v ↔ D.edgeData.selected θ.val u v)) := by
  let hE := inducedDiagram_forward hD ι
  let hn := inducedDiagram_naturalEdge_iff hD ι
  let hs := inducedDiagram_strictEndpoint_iff hD ι
  obtain ⟨ξ, hθξ, _, hξrel, hξno, hξcore⟩ :=
    exists_lastCliqueSweep hD θ (ι i) c (ι j) hac hce hae
  have hrestrict : inducedRestrict hE ι hn hs ξ = inducedRestrict hE ι hn hs θ := by
    apply fullSelection_injective
    ext e
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
      inducedRestrict_selected, inducedRestrict_selected]
    exact hξcore _ _ ((himage _).mp ⟨e.tail, rfl⟩) ((himage _).mp ⟨e.head, rfl⟩)
  let β := inducedExtend hD ι hn hs ξ α
  have hξβ : Relation.ReflTransGen (Flip D) ξ β := by
    apply induced_lift_reachable_of_last_gap hE hD ι hn hs ξ c (ι j) himage hξno
    simpa only [hrestrict] using hp
  have hβcover : Cover β (ι i) (ι j) :=
    (inducedExtend_cover_iff_of_last_gap hD ι hn hs ξ c (ι j) himage hξno α i j).mpr hαcover
  have hβrow : ∀ v, ι i < v → v ≤ c → ¬ D.edgeData.selected β.val (ι i) v := by
    intro v _ hvc hv
    obtain ⟨w, hw⟩ := (himage v).mpr (Or.inl hvc)
    have hα := (inducedExtend_inside hD ι hn hs ξ α i w).mp (hw.symm ▸ hv)
    exact hαrow w (hw.symm ▸ hvc) hα
  have hout : ∀ u v, ¬ ((u ≤ c ∨ u = ι j) ∧ (v ≤ c ∨ v = ι j)) →
      (D.edgeData.selected β.val u v ↔
        incomingSweepRelation (D.edgeData.selected θ.val) (ι i) c (ι j) u v) := by
    intro u v huv
    have hnot : ¬ ∃ a b, ι a = u ∧ ι b = v := by
      rintro ⟨a, b, ha, hb⟩
      exact huv ⟨(himage u).mp ⟨a, ha⟩, (himage v).mp ⟨b, hb⟩⟩
    exact (inducedExtend_outside hD ι hn hs ξ α u v hnot).trans (hξrel u v)
  obtain ⟨ζ, hβζ, _, hζrel⟩ := exists_outgoingSweep_of_le hD β
    (ι i) (ι j) (ι j) (hac.trans hce) le_rfl hβcover
  refine ⟨ζ, hθξ.trans (hξβ.trans hβζ), ?_, ?_⟩
  · intro u v
    rw [hζrel]
    exact (lastClique_restore_inside
      (fun {_ _} h => β.selected_lt_of_forward hD h) hβrow
      (ι u) (ι v) ((himage _).mp ⟨u, rfl⟩) ((himage _).mp ⟨v, rfl⟩)).trans
      (inducedExtend_inside hD ι hn hs ξ α u v)
  · intro u v hnot
    rw [hζrel]
    apply lastClique_restore_outside
      (fun {_ _} h => θ.selected_lt_of_forward hD h)
      hac hout hrow
    intro huv
    obtain ⟨a, ha⟩ := (himage u).mpr huv.1
    obtain ⟨b, hb⟩ := (himage v).mpr huv.2
    exact hnot ⟨a, b, ha, hb⟩

end VerticalStripLLT.Circular.DiagramProof

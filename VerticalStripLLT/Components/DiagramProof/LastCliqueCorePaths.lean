import VerticalStripLLT.Components.DiagramProof.LastCliqueTreeReplacement
import VerticalStripLLT.Components.DiagramProof.InducedCounts

/-! Fixed-exterior actual paths obtained from smaller-core uniqueness. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Equal-size anchors with the same exterior connect using smaller-core uniqueness. -/
theorem lastClique_reachable_of_same_exterior
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hgc : g.tail < c) (hcg : c < g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hτ : (allCorners D).Anchor hD τ)
    (hθconn : SelectedConnected
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ))
    (hτconn : SelectedConnected
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) τ))
    (htotal : totalSelected θ = totalSelected τ)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected θ.val u v ↔ D.edgeData.selected τ.val u v)) :
    Relation.ReflTransGen (Flip D) θ τ := by
  have hcoreθ : (allCorners (inducedDiagram hD ι)).Anchor
      (inducedDiagram_forward hD ι)
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
    simpa only [CornerFamily.induced_allCorners hD ι hcorners] using
      (allCorners D).anchor_inducedRestrict hD ι
        (fun e he => hcorners e ((allCorners D).corner e he)) θ hθ
  have hcoreτ : (allCorners (inducedDiagram hD ι)).Anchor
      (inducedDiagram_forward hD ι)
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) τ) := by
    simpa only [CornerFamily.induced_allCorners hD ι hcorners] using
      (allCorners D).anchor_inducedRestrict hD ι
        (fun e he => hcorners e ((allCorners D).corner e he)) τ hτ
  have houtcard :
      ((fullSelection θ).filter
        (fun e : Edge D.area => ¬ ∃ u v, ι u = e.tail ∧ ι v = e.head)).card =
      ((fullSelection τ).filter
        (fun e : Edge D.area => ¬ ∃ u v, ι u = e.tail ∧ ι v = e.head)).card := by
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hnot⟩
      refine ⟨?_, hnot⟩
      apply (mem_fullSelection_iff_selected τ e).mpr
      apply (houtside e.tail e.head hnot).mp
      exact (mem_fullSelection_iff_selected θ e).mp he
    · rintro ⟨he, hnot⟩
      refine ⟨?_, hnot⟩
      apply (mem_fullSelection_iff_selected θ e).mpr
      apply (houtside e.tail e.head hnot).mpr
      exact (mem_fullSelection_iff_selected τ e).mp he
  have hcorecount :
      totalSelected
          (inducedRestrict (inducedDiagram_forward hD ι) ι
            (inducedDiagram_naturalEdge_iff hD ι)
            (inducedDiagram_strictEndpoint_iff hD ι) θ) =
        totalSelected
          (inducedRestrict (inducedDiagram_forward hD ι) ι
            (inducedDiagram_naturalEdge_iff hD ι)
            (inducedDiagram_strictEndpoint_iff hD ι) τ) := by
    have hθall := totalSelected_eq_inducedRestrict_add_outside hD ι θ
    have hτall := totalSelected_eq_inducedRestrict_add_outside hD ι τ
    lia
  have hp := hunique _ _
    ((allCorners (inducedDiagram hD ι)).commonCover_of_anchor
      (inducedDiagram_forward hD ι) hcoreθ)
    ((allCorners (inducedDiagram hD ι)).commonCover_of_anchor
      (inducedDiagram_forward hD ι) hcoreτ)
    hθconn hτconn hcorecount
  obtain ⟨ζ, hpath, _, hinside, houtsideζ⟩ :=
    exists_lastClique_anchor_replacement_preserving_anchor hD ι c g hg hlast
      hgc hcg himage hcorners θ hθ
      (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) τ) hcoreτ hp
  have hfull : fullSelection ζ = fullSelection τ := by
    ext e
    by_cases hcore : ∃ a b, ι a = e.tail ∧ ι b = e.head
    · obtain ⟨a, b, ha, hb⟩ := hcore
      rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
      rw [← ha, ← hb, hinside]
      exact (inducedRestrict_selected (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) τ a b)
    · rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
      exact (houtsideζ e.tail e.head hcore).trans (houtside e.tail e.head hcore)
  have hζτ : ζ = τ := fullSelection_injective hfull
  simpa only [hζτ] using hpath

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.InitialVertex.Counts
import VerticalStripLLT.Components.DiagramProof.Foundation.WeakBlocks

/-! Fixed-extra-edge sectors connect by lifting the smaller core's actual paths. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

/-- With the initial row fixed, smaller-core uniqueness connects the ambient anchors. -/
theorem initialVertex_reachable_of_same_initial_row (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))),
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover α →
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hτ : (allCorners D).Anchor hD τ)
    (hcθ : SelectedConnected (initialVertexRestrict hD θ))
    (hcτ : SelectedConnected (initialVertexRestrict hD τ))
    (htotal : totalSelected θ = totalSelected τ)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ D.edgeData.selected τ.val 0 v) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let ι := Fin.succOrderEmb (k + 1)
  have hα := initialVertex_anchor_restrict hD f g hf hg hft hgt hfg θ hθ
  have hβ := initialVertex_anchor_restrict hD f g hf hg hft hgt hfg τ hτ
  have hp := hunique _ _
    ((allCorners (inducedDiagram hD ι)).commonCover_of_anchor
      (inducedDiagram_forward hD ι) hα)
    ((allCorners (inducedDiagram hD ι)).commonCover_of_anchor
      (inducedDiagram_forward hD ι) hβ)
    hcθ hcτ (initialVertex_core_count_eq hD θ τ htotal hrow)
  have hpath := initialVertex_lift_reachable hD θ (initialVertexRestrict hD τ) hp
  let ζ := inducedExtend hD ι (inducedDiagram_naturalEdge_iff hD ι)
    (inducedDiagram_strictEndpoint_iff hD ι) θ (initialVertexRestrict hD τ)
  have hζ : ζ = τ := by
    apply fullSelection_injective
    ext e
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
    by_cases ht : e.tail = 0
    · have hno : ¬ ∃ a b, ι a = e.tail ∧ ι b = e.head := by
        rintro ⟨a, _, ha, _⟩
        exact Fin.succ_ne_zero a (ha.trans ht)
      have hout := inducedExtend_outside hD ι (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ (initialVertexRestrict hD τ)
        e.tail e.head hno
      exact hout.trans (by simpa only [ht] using hrow e.head)
    · obtain ⟨u, v, hu, hv⟩ := (initialVertex_edge_retained_iff hD e).mpr ht
      rw [← hu, ← hv]
      exact (inducedExtend_inside hD ι (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ (initialVertexRestrict hD τ) u v).trans
        (initialVertexRestrict_selected hD τ u v)
  change Relation.ReflTransGen (Flip D) θ ζ at hpath
  simpa only [hζ] using hpath

end

end VerticalStripLLT.Circular.DiagramProof

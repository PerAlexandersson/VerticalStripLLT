import VerticalStripLLT.Components.DiagramProof.InitialVertex.Adjacent
import VerticalStripLLT.Components.DiagramProof.InitialVertex.CorePaths
import VerticalStripLLT.Components.DiagramProof.InitialVertex.Matching

/-! The crossing witness connects any two connected-core anchors in neighboring sectors. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {k : ℕ} {D : Diagram (k + 2)}

/-- Delete one initial extra, using only smaller-core uniqueness and removability
of its matching edge. The target's existence supplies the required free core position. -/
theorem initialVertex_reachable_of_erase_initial_row (hD : Forward D)
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
    (e : Edge D.area) (het : e.tail = 0) (he : e ∈ fullSelection θ)
    (hegood : (allCorners D).terminal hD e.tail < (allCorners D).terminal hD e.head)
    (hrow : (fullSelection τ).filter (fun q => q.tail = 0) =
      ((fullSelection θ).filter (fun q => q.tail = 0)).erase e)
    (hrem : ∀ d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area,
      (allCorners D).CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) →
      ((edgeSetGraph ((allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).goodEdges
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
          {s(d.tail, d.head)}).Connected) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let ι := Fin.succOrderEmb (k + 1)
  let E := inducedDiagram hD ι
  let F := allCorners D
  let F' := F.induced hD ι
  have hE := inducedDiagram_forward hD ι
  have hF' : F' = allCorners E := induced_allCorners_initialVertex hD f g hf hg hft hgt hfg
  have hfF : f ∈ F.edges := by simpa only [F, allCorners, Finset.mem_filter,
    Finset.mem_univ, true_and] using hf
  obtain ⟨d, hlink, _, hdF, hdgood, _⟩ :=
    F.exists_initial_matching_core_edge hD f e hfF hft het hegood
  have hcoreτ := initialVertex_anchor_restrict hD f g hf hg hft hgt hfg τ hτ
  have hupper : totalSelected (initialVertexRestrict hD τ) ≤
      (F'.goodEdges hE).card := by
    have hsub := ((allCorners E).anchor_iff_subsets hE
      (initialVertexRestrict hD τ)).mp hcoreτ
    rw [hF']
    exact Finset.card_le_card hsub.2
  have hcountθ := initialVertex_totalSelected hD θ
  have hcountτ := initialVertex_totalSelected hD τ
  have heRow : e ∈ (fullSelection θ).filter (fun q => q.tail = 0) :=
    Finset.mem_filter.mpr ⟨he, het⟩
  have herase := Finset.card_erase_add_one heRow
  have hroom : totalSelected (initialVertexRestrict hD θ) + 1 ≤
      (F'.goodEdges hE).card := by
    rw [hrow] at hcountτ
    lia
  have hunique' : ∀ α β : Orientation E,
      F'.CommonCover α → F'.CommonCover β → SelectedConnected α → SelectedConnected β →
      totalSelected α = totalSelected β → Relation.ReflTransGen (Flip E) α β := by
    simpa only [hF'] using hunique
  have hrem' : ((edgeSetGraph (F'.goodEdges hE)).deleteEdges {s(d.tail, d.head)}).Connected := by
    rw [hF']
    exact hrem d hlink
  obtain ⟨η, hp, hη, hcη, hrowη⟩ := F.exists_initialVertex_adjacent hD hunique'
    θ hθ hcθ e het he hegood d hlink ((F'.mem_goodEdges hE d).mpr hdgood) hdF hrem' hroom
  have hητ : (fullSelection η).filter (fun q => q.tail = 0) =
      (fullSelection τ).filter (fun q => q.tail = 0) := hrowη.trans hrow.symm
  apply hp.trans
  apply initialVertex_reachable_of_same_initial_row hD f g hf hg hft hgt hfg hunique
    η τ hη hτ hcη hcτ
  · exact (totalSelected_eq_of_reachable hp).symm.trans htotal
  · exact initialVertex_selected_row_iff η τ hητ

end VerticalStripLLT.Circular.DiagramProof

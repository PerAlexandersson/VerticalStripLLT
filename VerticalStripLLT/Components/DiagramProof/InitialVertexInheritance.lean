import VerticalStripLLT.Components.DiagramProof.InitialVertexSectors
import VerticalStripLLT.Components.DiagramProof.InitialVertexConnectedCore
import VerticalStripLLT.Components.DiagramProof.Preparation

/-! Initial-vertex inheritance by preparation, core joins and crossing slides between extra sets. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {k : ℕ} {D : Diagram (k + 2)}

/-- The written initial-vertex argument connects common-cover states of equal size.
Uniqueness is assumed only in the smaller core; the matching edges must be removable. -/
theorem commonCover_connected_of_initialVertex_core (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))),
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover α →
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) α β)
    (hrem : ∀ e ∈ (allCorners D).initialVertexExtras hD f,
      ∀ d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area,
      (allCorners D).CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) →
      ((edgeSetGraph ((allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).goodEdges
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
          {s(d.tail, d.head)}).Connected)
    (θ τ : Orientation D) (hθ : (allCorners D).CommonCover θ)
    (hτ : (allCorners D).CommonCover τ) (hcθ : SelectedConnected θ)
    (hcτ : SelectedConnected τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let F := allCorners D
  have hfF : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  obtain ⟨θ₁, hpθ₁, hθ₁, _⟩ := F.exists_preparation hD θ hθ
  obtain ⟨τ₁, hpτ₁, hτ₁, _⟩ := F.exists_preparation hD τ hτ
  obtain ⟨θ₂, hpθ₂, hθ₂, hcθ₂⟩ :=
    F.exists_reachable_connected_initialVertex_core hD f hfF hft θ₁ hθ₁
      ((selectedConnected_iff_of_reachable hpθ₁).mp hcθ)
  obtain ⟨τ₂, hpτ₂, hτ₂, hcτ₂⟩ :=
    F.exists_reachable_connected_initialVertex_core hD f hfF hft τ₁ hτ₁
      ((selectedConnected_iff_of_reachable hpτ₁).mp hcτ)
  have hpθ := hpθ₁.trans hpθ₂
  have hpτ := hpτ₁.trans hpτ₂
  have hsize : totalSelected θ₂ = totalSelected τ₂ :=
    (totalSelected_eq_of_reachable hpθ).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hpτ))
  have hp := initialVertex_connected_core_anchors hD f g hf hg hft hgt hfg hunique hrem
    θ₂ τ₂ hθ₂ hτ₂ hcθ₂ hcτ₂ hsize
  exact hpθ.trans (hp.trans (flip_reachable_symm hpτ))

end VerticalStripLLT.Circular.DiagramProof

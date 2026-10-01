import VerticalStripLLT.Components.DiagramProof.LastCliqueInheritance
import VerticalStripLLT.Components.DiagramProof.ReversedPaths
import VerticalStripLLT.Components.DiagramProof.ReversedEmbedding

/-! First-clique inheritance by reflecting the last-clique diagram proof. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Retain the first vertex and the vertices from the second corner tail onwards.
The induction hypothesis concerns exactly this retained core, in reversed order. -/
theorem commonCover_connected_of_firstClique_core
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (f g : Edge D.area)
    (hf : IsCorner f) (hg : IsCorner g) (hfirst : ∀ v : Fin n, f.tail ≤ v)
    (hcross : f.tail < g.tail ∧ g.tail < f.head ∧ f.head < g.head)
    (hafter : ∀ e : Edge D.area, IsCorner e → e ≠ f → g.tail ≤ e.tail)
    (himage : ∀ z, (∃ w, ι w = z) ↔ g.tail ≤ z ∨ z = f.tail)
    (hunique : ∀ α β : Orientation
        (inducedDiagram (reversedDiagram_forward hD) (reverseOrderEmbedding ι)),
      (allCorners (inducedDiagram (reversedDiagram_forward hD)
        (reverseOrderEmbedding ι))).CommonCover α →
      (allCorners (inducedDiagram (reversedDiagram_forward hD)
        (reverseOrderEmbedding ι))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram (reversedDiagram_forward hD)
        (reverseOrderEmbedding ι))) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).CommonCover θ)
    (hτ : (allCorners D).CommonCover τ) (hcθ : SelectedConnected θ)
    (hcτ : SelectedConnected τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let ρ := reverseEdgeEquiv hD
  have hlast : ∀ v : Fin n, v ≤ (ρ f).head := by
    intro v
    rw [reverseEdgeEquiv_head]
    simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr (hfirst v.rev)
  have hcross' : (ρ g).tail < (ρ f).tail ∧ (ρ f).tail < (ρ g).head ∧
      (ρ g).head < (ρ f).head := by
    dsimp only [ρ]
    rw [reverseEdgeEquiv_tail, reverseEdgeEquiv_tail,
      reverseEdgeEquiv_head, reverseEdgeEquiv_head]
    exact ⟨Fin.rev_lt_rev.mpr hcross.2.2, Fin.rev_lt_rev.mpr hcross.2.1,
      Fin.rev_lt_rev.mpr hcross.1⟩
  have hbefore : ∀ e : Edge (reversedDiagram hD).area,
      IsCorner e → e ≠ ρ f → e.head ≤ (ρ g).head := by
    intro e he hne
    obtain ⟨d, rfl⟩ := ρ.surjective e
    have hd := (reverseEdgeEquiv_isCorner_iff hD d).mp he
    have hdf : d ≠ f := fun h => hne (congrArg ρ h)
    dsimp only [ρ]
    rw [reverseEdgeEquiv_head, reverseEdgeEquiv_head]
    exact Fin.rev_le_rev.mpr (hafter d hd hdf)
  have himage' : ∀ z, (∃ w, reverseOrderEmbedding ι w = z) ↔
      z ≤ (ρ g).head ∨ z = (ρ f).head := by
    simpa only [ρ, reverseEdgeEquiv_head] using
      reverseOrderEmbedding_prefix_image ι himage
  apply (reversedOrientation_reachable_iff hD θ τ).mp
  apply commonCover_connected_of_lastClique_core (reversedDiagram_forward hD)
    (reverseOrderEmbedding ι) (ρ g) (ρ f)
    ((reverseEdgeEquiv_isCorner_iff hD g).mpr hg)
    ((reverseEdgeEquiv_isCorner_iff hD f).mpr hf)
    hlast hcross' hbefore himage' hunique
    (reversedOrientation hD θ) (reversedOrientation hD τ)
    ((reversedOrientation_commonCover hD θ).mpr hθ)
    ((reversedOrientation_commonCover hD τ).mpr hτ)
    ((reversedOrientation_connected hD θ).mpr hcθ)
    ((reversedOrientation_connected hD τ).mpr hcτ)
  simpa only [reversedOrientation_totalSelected] using htotal

end

end VerticalStripLLT.Circular.DiagramProof

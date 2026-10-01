import VerticalStripLLT.Components.DiagramProof.ReversedDiagram
import VerticalStripLLT.Components.DiagramProof.OrderReversal

/-! Exact path correspondence between an ordinary diagram and its reflection. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Reflect the diagram and every selected edge, retaining its strict markings. -/
def reversedOrientation (hD : Forward D) : Orientation D ≃ Orientation (reversedDiagram hD) :=
  reverseOrientationEquiv hD (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD)

@[simp]
theorem reversedOrientation_totalSelected (hD : Forward D) (θ : Orientation D) :
    totalSelected (reversedOrientation hD θ) = totalSelected θ :=
  totalSelected_reverseOrientation (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD) θ

theorem reversedOrientation_selected (hD : Forward D) (θ : Orientation D) (u v : Fin n) :
    (reversedDiagram hD).edgeData.selected (reversedOrientation hD θ).val u v ↔
      D.edgeData.selected θ.val v.rev u.rev :=
  reverseOrientation_selected (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD) (reverseEdgeEquiv_tail hD) (reverseEdgeEquiv_head hD) θ u v

theorem reversedOrientation_cover (hD : Forward D) (θ : Orientation D) (u v : Fin n) :
    Cover (reversedOrientation hD θ) u v ↔ Cover θ v.rev u.rev :=
  reverseOrientation_cover (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD) (reverseEdgeEquiv_tail hD) (reverseEdgeEquiv_head hD) θ u v

theorem reversedOrientation_connected (hD : Forward D) (θ : Orientation D) :
    SelectedConnected (reversedOrientation hD θ) ↔ SelectedConnected θ :=
  reverseOrientation_connected (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD) (reverseEdgeEquiv_tail hD) (reverseEdgeEquiv_head hD) θ

theorem reversedOrientation_commonCover (hD : Forward D) (θ : Orientation D) :
    (allCorners (reversedDiagram hD)).CommonCover (reversedOrientation hD θ) ↔
      (allCorners D).CommonCover θ :=
  reverseOrientation_commonCover (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD) (reverseEdgeEquiv_tail hD) (reverseEdgeEquiv_head hD)
    (reverseEdgeEquiv_isCorner_iff hD) θ

/-- Reflection carries the complete actual path relation in both directions. -/
theorem reversedOrientation_reachable_iff (hD : Forward D) (θ η : Orientation D) :
    Relation.ReflTransGen (Flip (reversedDiagram hD))
      (reversedOrientation hD θ) (reversedOrientation hD η) ↔
      Relation.ReflTransGen (Flip D) θ η :=
  reverseOrientation_reachable_iff hD (reversedDiagram_forward hD) (reverseEdgeEquiv hD)
    (reverseEdgeEquiv_strict_iff hD)
    (reverseEdgeEquiv_tail hD) (reverseEdgeEquiv_head hD) θ η

/-- Reflection maps a whole component onto the whole component of its reflected state. -/
theorem reversedOrientation_map_flipComponent (hD : Forward D) (θ : Orientation D) :
    (flipComponent D θ).map (reversedOrientation hD).toEmbedding =
      flipComponent (reversedDiagram hD) (reversedOrientation hD θ) := by
  classical
  ext η
  obtain ⟨τ, rfl⟩ := (reversedOrientation hD).surjective η
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_flipComponent_iff,
    reversedOrientation_reachable_iff]

end

end VerticalStripLLT.Circular.DiagramProof

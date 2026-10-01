import VerticalStripLLT.Components.DiagramProof.ClosedInducedAnchors
import VerticalStripLLT.Components.DiagramProof.InitialVertexCorners

/-! Restricting anchors and lifting actual paths after deleting the first vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k : ℕ} {D : Diagram (k + 2)}

/-- The actual selected diagram on the vertices after zero. -/
noncomputable def initialVertexRestrict (hD : Forward D) (θ : Orientation D) :
    Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))) :=
  inducedRestrict (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))
    (Fin.succOrderEmb (k + 1))
    (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
    (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ

theorem initialVertexRestrict_selected (hD : Forward D) (θ : Orientation D)
    (u v : Fin (k + 1)) :
    (inducedDiagram hD (Fin.succOrderEmb (k + 1))).edgeData.selected
      (initialVertexRestrict hD θ).val u v ↔ D.edgeData.selected θ.val u.succ v.succ :=
  inducedRestrict_selected ..

/-- A forward path between positive vertices cannot pass through zero. -/
theorem convex_succOrderEmb (m : ℕ) : ConvexImage (Fin.succOrderEmb m) := by
  intro u v z huz _
  have hz : z ≠ 0 := ne_of_gt ((Fin.succ_pos u).trans_le huz)
  obtain ⟨w, hw⟩ := Fin.eq_succ_of_ne_zero hz
  exact ⟨w, hw.symm⟩

namespace CornerFamily

/-- The vertices remaining after deletion of zero are closed under corner successors. -/
theorem initialVertex_step_closed (F : CornerFamily D) (hD : Forward D)
    (u : Fin (k + 1)) (v : Fin (k + 2)) (h : F.step u.succ v) :
    ∃ w : Fin (k + 1), (Fin.succOrderEmb (k + 1)) w = v := by
  have hv : v ≠ 0 := ne_of_gt ((Fin.succ_pos u).trans (F.step_forward hD h))
  obtain ⟨w, hw⟩ := Fin.eq_succ_of_ne_zero hv
  exact ⟨w, hw.symm⟩

theorem initialVertex_terminal (F : CornerFamily D) (hD : Forward D) (u : Fin (k + 1)) :
    ((F.induced hD (Fin.succOrderEmb (k + 1))).terminal
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) u).succ =
      F.terminal hD u.succ :=
  F.terminal_induced_of_closed hD (Fin.succOrderEmb (k + 1))
    (F.initialVertex_step_closed hD) u

end CornerFamily

/-- Deletion of zero restricts an ambient anchor to an anchor of the actual core. -/
theorem initialVertex_anchor_restrict (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (θ : Orientation D) (hθ : (allCorners D).Anchor hD θ) :
    (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).Anchor
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))
      (inducedRestrict (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))
        (Fin.succOrderEmb (k + 1))
        (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
        (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ) := by
  simpa only [induced_allCorners_initialVertex hD f g hf hg hft hgt hfg] using
    (allCorners D).anchor_inducedRestrict_of_closed hD (Fin.succOrderEmb (k + 1))
      ((allCorners D).initialVertex_step_closed hD) θ hθ

/-- Every actual core path lifts with all edges at zero fixed, including its strict corner. -/
theorem initialVertex_lift_reachable (hD : Forward D) (θ : Orientation D)
    (α : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))))
    (hpath : Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1))))
      (inducedRestrict (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))
        (Fin.succOrderEmb (k + 1))
        (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
        (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ) α) :
    Relation.ReflTransGen (Flip D) θ
      (inducedExtend hD (Fin.succOrderEmb (k + 1))
        (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
        (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ α) := by
  apply induced_lift_reachable (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1)))
    hD (Fin.succOrderEmb (k + 1))
    (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
    (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ ?_ hpath
  intro β u v
  apply relationCover_iff_of_convexImage (Fin.succOrderEmb (k + 1))
    (convex_succOrderEmb (k + 1))
    (fun {_ _} hs => Orientation.selected_lt_of_forward _ hD hs)
    (fun x y => (inducedExtend_inside hD (Fin.succOrderEmb (k + 1))
      (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)))
      (inducedDiagram_strictEndpoint_iff hD (Fin.succOrderEmb (k + 1))) θ β x y).symm)

end VerticalStripLLT.Circular.DiagramProof

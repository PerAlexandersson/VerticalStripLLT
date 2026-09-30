import VerticalStripLLT.Components.DiagramProof.CoreConnectivity
import VerticalStripLLT.Components.DiagramProof.InducedDecorations
import VerticalStripLLT.Components.DiagramProof.InducedRestriction
import VerticalStripLLT.Components.DiagramProof.LastCliqueEdges
import VerticalStripLLT.Components.DiagramProof.WeakBlocks

/-! Connectivity of the core from connected intersections with last-clique blocks. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Every selected edge lies in the last clique or has both endpoints in the core. -/
theorem selected_in_last_clique_or_core
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (x y : Fin n) (hxy : D.edgeData.selected θ.val x y) :
    (g.tail ≤ x ∧ y ≤ g.head ∧ D.edgeData.selected θ.val x y) ∨
      ∃ u v, ι u = x ∧ ι v = y := by
  obtain ⟨e, he, rfl, rfl⟩ := hxy
  rcases naturalEdge_in_last_clique_or_core hD g c hbefore e with hclique | hcore
  · exact Or.inl ⟨hclique.1, hclique.2, e, he, rfl, rfl⟩
  · obtain ⟨u, hu⟩ := (himage e.tail).mpr (Or.inl hcore.1)
    obtain ⟨v, hv⟩ := (himage e.head).mpr (Or.inl hcore.2)
    exact Or.inr ⟨u, v, hu, hv⟩

/-- Each last-clique selected block meets the core of a connected orientation. -/
theorem lastClique_block_meets_core
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hconn : SelectedConnected θ) (x : Fin n) :
    ∃ u, Relation.EqvGen
      (fun a b => g.tail ≤ a ∧ b ≤ g.head ∧ D.edgeData.selected θ.val a b)
      x (ι u) := by
  exact coreRepresentative_exists_of_connected (0 : Fin (k + 1))
    (selected_in_last_clique_or_core hD ι c g hbefore himage θ) hconn x

/-- Connecting the core intersection of every last-clique block connects the full core. -/
theorem selectedConnected_inducedRestrict_of_lastClique_blocks
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hconn : SelectedConnected θ)
    (hblock : ∀ u v, Relation.EqvGen
      (fun a b => g.tail ≤ a ∧ b ≤ g.head ∧ D.edgeData.selected θ.val a b)
      (ι u) (ι v) → WeakReach
        (inducedRestrict (inducedDiagram_forward hD ι) ι
          (inducedDiagram_naturalEdge_iff hD ι)
          (inducedDiagram_strictEndpoint_iff hD ι) θ) u v) :
    SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
  apply coreConnected_of_block_gluing_of_connected (0 : Fin (k + 1))
    (ι := ι) (S := D.edgeData.selected θ.val)
    (L := fun a b => g.tail ≤ a ∧ b ≤ g.head ∧ D.edgeData.selected θ.val a b)
  · intro u v huv
    exact (inducedRestrict_selected (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ u v).mpr huv
  · exact selected_in_last_clique_or_core hD ι c g hbefore himage θ
  · exact hblock
  · exact hconn

end

end VerticalStripLLT.Circular.DiagramProof

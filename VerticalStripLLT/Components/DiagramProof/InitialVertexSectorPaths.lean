import VerticalStripLLT.Components.DiagramProof.InitialVertexAdjacentPaths
import VerticalStripLLT.Components.DiagramProof.InitialVertexExtras

/-! Passing between the extra-edge subsets and the exact initial-row path statements. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

variable {k : ℕ} {D : Diagram (k + 2)}

namespace CornerFamily

theorem initialVertex_extra_good (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (e : Edge D.area) (he : e ∈ F.initialVertexExtras hD f) :
    e.tail = 0 ∧ e ≠ f ∧ F.terminal hD e.tail < F.terminal hD e.head := by
  obtain ⟨heG, het, hef⟩ := Finset.mem_filter.mp he
  have hen : e ∉ F.edges := by
    intro heF
    have ht : e.tail = f.tail := het.trans hft.symm
    have hh := F.step_rightUnique
      ((F.step_iff _ _).mpr ⟨e, heF, rfl, rfl⟩)
      ((F.step_iff _ _).mpr ⟨f, hf, ht.symm, rfl⟩)
    exact hef (D.endpointEmbedding.injective (Prod.ext ht hh))
  exact ⟨het, hef, ((F.mem_goodEdges hD e).mp heG).resolve_left hen⟩

end CornerFamily

/-- Deleting an extra from the selected extra set is precisely the neighboring-row move. -/
theorem initialVertex_reachable_of_erase_extras (hD : Forward D)
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
    (e : Edge D.area) (he : e ∈ selectedInitialVertexExtras θ f)
    (hextras : selectedInitialVertexExtras τ f = (selectedInitialVertexExtras θ f).erase e)
    (hrem : ∀ d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area,
      (allCorners D).CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) →
      ((edgeSetGraph ((allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).goodEdges
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
          {s(d.tail, d.head)}).Connected) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let F := allCorners D
  have hfF : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have heJ := F.selectedInitialVertexExtras_subset hD θ hθ f he
  obtain ⟨het, hef, hegood⟩ := F.initialVertex_extra_good hD f hfF hft e heJ
  have hesel : e ∈ fullSelection θ := (Finset.mem_filter.mp (Finset.mem_erase.mp he).2).1
  apply initialVertex_reachable_of_erase_initial_row hD f g hf hg hft hgt hfg hunique
    θ τ hθ hτ hcθ hcτ htotal e het hesel hegood ?_ hrem
  rw [F.row_eq_insert_selectedInitialVertexExtras hD θ hθ f hfF hft,
    F.row_eq_insert_selectedInitialVertexExtras hD τ hτ f hfF hft, hextras]
  ext q
  simp only [Finset.mem_insert, Finset.mem_erase]
  grind

end VerticalStripLLT.Circular.DiagramProof

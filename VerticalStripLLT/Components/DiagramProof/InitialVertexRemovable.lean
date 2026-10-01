import VerticalStripLLT.Components.DiagramProof.InitialVertexChainCount
import VerticalStripLLT.Components.DiagramProof.InitialVertexNaturalEdges
import VerticalStripLLT.Components.DiagramProof.InitialVertexInheritance
import VerticalStripLLT.Components.DiagramProof.RemovableGoodEdges

/-! The no-articulation short edges and three corner chains supply initial-core removability. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

variable {k : ℕ} {D : Diagram (k + 2)}

namespace CornerFamily

/-- Deleting zero retains the third chain needed to go around any good non-corner core edge. -/
theorem initialVertex_goodEdgeGraph_delete_connected (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (hshort : ∀ u v : Fin (k + 2), u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := D) u v)
    (hchains : 3 ≤ Nat.card {v : Fin (k + 2) // F.terminal hD v = v})
    (d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area)
    (hdG : d ∈ (F.induced hD (Fin.succOrderEmb (k + 1))).goodEdges
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))
    (hdF : d ∉ (F.induced hD (Fin.succOrderEmb (k + 1))).edges) :
    ((edgeSetGraph ((F.induced hD (Fin.succOrderEmb (k + 1))).goodEdges
      (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
        {s(d.tail, d.head)}).Connected := by
  let ι := Fin.succOrderEmb (k + 1)
  let G := F.induced hD ι
  have hE := inducedDiagram_forward hD ι
  have hcount : 3 ≤ Nat.card {u : Fin (k + 1) // G.terminal hE u = u} := by
    rw [F.initialVertex_fixedTerminal_card hD f hf hft]
    exact hchains
  have hbound : Nat.card {u : Fin (k + 1) // G.terminal hE u = u} ≤ k + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Nat.card_le_card_of_injective
        (fun u : {u : Fin (k + 1) // G.terminal hE u = u} => u.val) Subtype.val_injective)
  exact G.goodEdgeGraph_delete_connected hE (hcount.trans hbound)
    (initialVertex_induced_short_naturalEdges hD hshort) d hdG hdF
    (G.exists_third_terminal hE hcount d.tail d.head)

end CornerFamily

/-- The initial-vertex branch needs only the smaller-core induction hypothesis
once the short natural edges and three corner chains are known. -/
theorem commonCover_connected_of_initialVertex_short (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (hshort : ∀ u v : Fin (k + 2), u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := D) u v)
    (hchains : 3 ≤ Nat.card {v : Fin (k + 2) // (allCorners D).terminal hD v = v})
    (hunique : ∀ α β : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))),
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover α →
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).CommonCover θ)
    (hτ : (allCorners D).CommonCover τ) (hcθ : SelectedConnected θ)
    (hcτ : SelectedConnected τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  apply commonCover_connected_of_initialVertex_core hD f g hf hg hft hgt hfg hunique
    ?_ θ τ hθ hτ hcθ hcτ htotal
  intro e he d hlink
  let F := allCorners D
  let ι := Fin.succOrderEmb (k + 1)
  have hE := inducedDiagram_forward hD ι
  have hfF : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  obtain ⟨_, _, hegood⟩ := F.initialVertex_extra_good hD f hfF hft e he
  have hdF : d ∉ (F.induced hD ι).edges := by
    intro hd
    exact (F.copyLink_not_mem hlink).2 ((F.mem_induced_edges hD ι d).mp hd)
  have hdG : d ∈ (F.induced hD ι).goodEdges hE := by
    apply ((F.induced hD ι).mem_goodEdges hE d).mpr
    apply (F.goodEdge_induced_iff_of_closed hD ι (F.initialVertex_step_closed hD) d).mpr
    right
    rw [← F.terminal_eq_of_step hD hlink.1,
      ← F.terminal_eq_of_step hD hlink.2.1]
    exact hegood
  have hremove := F.initialVertex_goodEdgeGraph_delete_connected hD f hfF hft
    hshort hchains d hdG hdF
  change ((edgeSetGraph ((F.induced hD ι).goodEdges hE)).deleteEdges
    {s(d.tail, d.head)}).Connected at hremove
  have hF := induced_allCorners_initialVertex hD f g hf hg hft hgt hfg
  change F.induced hD ι = allCorners (inducedDiagram hD ι) at hF
  rw [hF] at hremove
  exact hremove

end VerticalStripLLT.Circular.DiagramProof

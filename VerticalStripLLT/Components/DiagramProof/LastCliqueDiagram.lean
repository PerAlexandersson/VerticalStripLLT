import VerticalStripLLT.Components.DiagramProof.InducedDecorations
import VerticalStripLLT.Components.DiagramProof.LastCliqueEmbedding

/-! The decorated core obtained by retaining a prefix and the final vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

noncomputable section

variable {n : ℕ} {D : Diagram n} (hD : Forward D)

def lastCliqueDiagram (c e : Fin n) (hce : c < e) : Diagram (c.val + 2) :=
  inducedDiagram hD (lastCliqueEmbed c e hce)

include hD in
/-- If only the last maximal corner ends beyond the prefix, all corner endpoints survive. -/
theorem lastClique_corner_endpoints (c : Fin n) (g : Edge D.area)
    (hcg : c < g.head) (hgc : g.tail ≤ c)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (f : Edge D.area) (hf : IsCorner f) :
    ∃ u v, lastCliqueEmbed c g.head hcg u = f.tail ∧
      lastCliqueEmbed c g.head hcg v = f.head := by
  have htail : f.tail ≤ c := by
    by_cases hfg : f = g
    · simpa only [hfg] using hgc
    · exact (hD f).le.trans (hbefore f hf hfg)
  have hhead : f.head ≤ c ∨ f.head = g.head := by
    by_cases hfg : f = g
    · exact Or.inr (congrArg Edge.head hfg)
    · exact Or.inl (hbefore f hf hfg)
  obtain ⟨u, hu⟩ := (lastCliqueEmbed_image c g.head hcg f.tail).mpr (Or.inl htail)
  obtain ⟨v, hv⟩ := (lastCliqueEmbed_image c g.head hcg f.head).mpr hhead
  exact ⟨u, v, hu, hv⟩

/-- The last-clique core has exactly the inherited maximal corners. -/
theorem lastCliqueDiagram_corner_iff (c : Fin n) (g : Edge D.area)
    (hcg : c < g.head) (hgc : g.tail ≤ c)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (f : Edge (lastCliqueDiagram hD c g.head hcg).area) :
    IsCorner (inducedEdge hD (lastCliqueEmbed c g.head hcg) f) ↔ IsCorner f :=
  inducedEdge_isCorner_iff hD (lastCliqueEmbed c g.head hcg)
    (lastClique_corner_endpoints hD c g hcg hgc hbefore) f

/-- Deleting at least one vertex in the last gap gives the smaller vertex count for induction. -/
theorem lastCliqueDiagram_size_lt (c e : Fin n) (hgap : c.val + 1 < e.val) :
    c.val + 2 < n := by
  have he := e.isLt
  lia

end

end VerticalStripLLT.Circular.DiagramProof

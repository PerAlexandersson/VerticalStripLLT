import VerticalStripLLT.Components.DiagramProof.InducedCorners

/-! Natural edges lie in the prefix core or beneath the final maximal corner. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

theorem naturalEdge_in_last_clique_or_core (hD : Forward D) (g : Edge D.area)
    (c : Fin n) (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (e : Edge D.area) :
    (g.tail ≤ e.tail ∧ e.head ≤ g.head) ∨ (e.tail ≤ c ∧ e.head ≤ c) := by
  obtain ⟨f, hf, htail, hhead⟩ := exists_corner_containing hD e
  by_cases hfg : f = g
  · subst f
    exact Or.inl ⟨htail, hhead⟩
  · right
    have hfc : f.head ≤ c := hbefore f hf hfg
    exact ⟨(hD e).le.trans (hhead.trans hfc), hhead.trans hfc⟩

end VerticalStripLLT.Circular.DiagramProof

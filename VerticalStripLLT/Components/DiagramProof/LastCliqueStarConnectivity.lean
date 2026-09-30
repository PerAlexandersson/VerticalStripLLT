import VerticalStripLLT.Components.DiagramProof.LastCliqueCoreConnectivity
import VerticalStripLLT.Components.DiagramProof.CliqueBlockBounds

/-! The prepared star makes the whole last-clique interval one weak block. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Every vertex in the last-clique interval reaches its last vertex. -/
theorem lastClique_block_connected_of_star
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hconn : SelectedConnected θ)
    (hstar : ∀ u, g.tail ≤ ι u → ι u < g.head →
      D.edgeData.selected θ.val (ι u) g.head) :
    ∀ x, g.tail ≤ x → x ≤ g.head →
      Relation.EqvGen (cliqueBlockRelation g θ) x g.head := by
  intro x hxlo hxhi
  obtain ⟨u, hpath⟩ := lastClique_block_meets_core hD ι c g hbefore himage θ hconn x
  have hpath' : Relation.EqvGen (cliqueBlockRelation g θ) x (ι u) :=
    Relation.EqvGen.mono
      (fun a b hab => (cliqueBlockRelation_iff_of_forward hD g θ a b).mpr hab)
      _ _ hpath
  have hu_bounds : g.tail ≤ ι u ∧ ι u ≤ g.head := by
    rcases eqvGen_cliqueBlockRelation_eq_or_bounds g θ hpath' with heq | hbounds
    · simpa only [← heq] using And.intro hxlo hxhi
    · exact hbounds.2
  have hto : Relation.EqvGen (cliqueBlockRelation g θ) (ι u) g.head := by
    by_cases hhead : ι u = g.head
    · exact hhead ▸ Relation.EqvGen.refl _
    · have hlt : ι u < g.head := lt_of_le_of_ne hu_bounds.2 hhead
      apply Relation.EqvGen.rel
      exact (cliqueBlockRelation_iff_of_forward hD g θ (ι u) g.head).mpr
        ⟨hu_bounds.1, le_rfl, hstar u hu_bounds.1 hlt⟩
  exact Relation.EqvGen.trans _ _ _ hpath' hto

end

end VerticalStripLLT.Circular.DiagramProof

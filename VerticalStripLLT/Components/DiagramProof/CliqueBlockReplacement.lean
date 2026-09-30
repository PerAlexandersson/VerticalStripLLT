import VerticalStripLLT.Components.DiagramProof.BlockReplacement
import VerticalStripLLT.Components.DiagramProof.CliqueRestriction
import VerticalStripLLT.Components.DiagramProof.WeakBlocks

/-! Weak-block preservation for an internally connected clique replacement. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- The selected relation restricted to the interval of a natural edge. -/
def cliqueBlockRelation (e : Edge D.area) (θ : Orientation D) (x y : Fin n) : Prop :=
  (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) ∧
    D.edgeData.selected θ.val x y

theorem cliqueBlock_weakReach_iff
    (e : Edge D.area) (ι : Fin (k + 1) ↪o Fin n)
    (hbounds : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head)
    (θ η : Orientation D)
    (hblock : ∀ z, (∃ i, ι i = z) ↔
      Relation.EqvGen (cliqueBlockRelation e θ) (ι 0) z)
    (α : Orientation (completeDiagram k))
    (hαconn : SelectedConnected α)
    (hinside : ∀ u v, D.edgeData.selected η.val (ι u) (ι v) ↔
      (completeDiagram k).edgeData.selected α.val u v)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v))
    (x y : Fin n) :
    Relation.EqvGen (cliqueBlockRelation e θ) x y ↔
      Relation.EqvGen (cliqueBlockRelation e η) x y := by
  let R := cliqueBlockRelation e θ
  let S := cliqueBlockRelation e η
  have hR : ∀ u v, Relation.EqvGen R (ι u) (ι v) := by
    intro u v
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ ((hblock (ι u)).mp ⟨u, rfl⟩))
      ((hblock (ι v)).mp ⟨v, rfl⟩)
  have hSedge : ∀ u v,
      (completeDiagram k).edgeData.selected α.val u v →
        Relation.EqvGen S (ι u) (ι v) := by
    intro u v huv
    exact Relation.EqvGen.rel _ _ ⟨hbounds u, hbounds v, (hinside u v).mpr huv⟩
  have hS : ∀ u v, Relation.EqvGen S (ι u) (ι v) := by
    intro u v
    exact Relation.EqvGen.eqvGen_le hSedge u v (hαconn u v)
  have hout : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (R u v ↔ S u v) := by
    intro u v huv
    simp only [R, S, cliqueBlockRelation, houtside u v huv]
  exact eqvGen_iff_of_block_replacement ι R S hR hS hout x y

end

end VerticalStripLLT.Circular.DiagramProof

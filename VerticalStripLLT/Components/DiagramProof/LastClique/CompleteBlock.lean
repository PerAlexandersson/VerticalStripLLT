import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueRestriction
import VerticalStripLLT.Components.DiagramProof.Corners.CliqueEdges
import VerticalStripLLT.Components.DiagramProof.LastClique.BlockPaths
import VerticalStripLLT.Components.DiagramProof.Complete.Connectivity

/-! Complete-diagram connectivity localized to a selected weak block of a natural clique. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {D : Diagram n}

/-- Selected paths in the replaced core cannot leave its block inside the ambient interval. -/
theorem cliqueExtend_cover_iff_of_closed (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (hnatural : ∀ a b, a < b → ∃ e : Edge D.area, e.tail = ι a ∧ e.head = ι b)
    (θ : Orientation D) (lo hi : Fin n) (hbounds : ∀ i, lo ≤ ι i ∧ ι i ≤ hi)
    (hclosed : ∀ x y, lo ≤ x → y ≤ hi → D.edgeData.selected θ.val x y →
      (∃ i, ι i = x) → ∃ j, ι j = y)
    (α : Orientation (completeDiagram k)) (u v : Fin (k + 1)) :
    Cover (cliqueExtend hD ι hnatural θ α) (ι u) (ι v) ↔ Cover α u v := by
  apply relationCover_iff_of_pathImage ι
    (pathImage_closed_of_forward_update ι
      (fun {_ _} h => (cliqueExtend hD ι hnatural θ α).selected_lt_of_forward hD h)
      hbounds hclosed (cliqueExtend_outside hD ι hnatural θ α))
    (fun a b => (cliqueExtend_inside hD ι hnatural θ α a b).symm)

/-- A whole selected weak block in a clique becomes a connected complete-core state. -/
theorem cliqueRestrict_connected_of_block (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (θ : Orientation D) (lo hi : Fin n) (hbounds : ∀ i, lo ≤ ι i ∧ ι i ≤ hi)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (lo ≤ x ∧ x ≤ hi) ∧ (lo ≤ y ∧ y ≤ hi) ∧
        D.edgeData.selected θ.val x y) (ι 0) z) :
    SelectedConnected (cliqueRestrict hD ι θ) := by
  let R := fun x y => (lo ≤ x ∧ x ≤ hi) ∧ (lo ≤ y ∧ y ≤ hi) ∧
    D.edgeData.selected θ.val x y
  have hclosed : ∀ x y, R x y → ((∃ i, ι i = x) ↔ ∃ j, ι j = y) := by
    intro x y hxy
    rw [hblock x, hblock y]
    exact ⟨fun hx => Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ hxy),
      fun hy => Relation.EqvGen.trans _ _ _ hy
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hxy))⟩
  have hrel : ∀ a b,
      (completeDiagram k).edgeData.selected (cliqueRestrict hD ι θ).val a b ↔ R (ι a) (ι b) := by
    intro a b
    rw [cliqueRestrict_selected]
    exact ⟨fun h => ⟨hbounds a, hbounds b, h⟩, fun h => h.2.2⟩
  intro u v
  apply (eqvGen_iff_of_image_closed ι.toEmbedding hclosed hrel u v).mp
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ ((hblock (ι u)).mp ⟨u, rfl⟩))
    ((hblock (ι v)).mp ⟨v, rfl⟩)

/-- A selected edge inside the clique cannot leave the chosen whole weak block. -/
theorem selected_image_closed_of_block (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (θ : Orientation D) (lo hi : Fin n)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (lo ≤ x ∧ x ≤ hi) ∧ (lo ≤ y ∧ y ≤ hi) ∧
        D.edgeData.selected θ.val x y) (ι 0) z)
    (x y : Fin n) (hlox : lo ≤ x) (hyhi : y ≤ hi)
    (hxy : D.edgeData.selected θ.val x y) (hx : ∃ i, ι i = x) : ∃ j, ι j = y := by
  have hlt := θ.selected_lt_of_forward hD hxy
  apply (hblock y).mpr
  exact Relation.EqvGen.trans _ _ _ ((hblock x).mp hx)
    (Relation.EqvGen.rel _ _ ⟨⟨hlox, hlt.le.trans hyhi⟩,
      ⟨hlox.trans hlt.le, hyhi⟩, hxy⟩)

/-- Two connected configurations of one selected clique block with the same local edge count
and the same extreme cover connect by actual ambient flips. Their exterior selections agree. -/
theorem clique_reachable_of_block (hD : Forward D) (e : Edge D.area)
    (ι : Fin (k + 1) ↪o Fin n) (hbounds : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head)
    (θ η : Orientation D)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) ∧
        D.edgeData.selected θ.val x y) (ι 0) z)
    (hη : SelectedConnected (cliqueRestrict hD ι η))
    (hcθ : Cover θ (ι 0) (ι (Fin.last k))) (hcη : Cover η (ι 0) (ι (Fin.last k)))
    (htotal : totalSelected (cliqueRestrict hD ι θ) = totalSelected (cliqueRestrict hD ι η))
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v)) :
    Relation.ReflTransGen (Flip D) θ η := by
  have hnatural (a b : Fin (k + 1)) (hab : a < b) :
      ∃ f : Edge D.area, f.tail = ι a ∧ f.head = ι b :=
    exists_edge_of_orderEmbedding_mem_interval hD e ι hbounds hab
  have hclosed := selected_image_closed_of_block hD ι θ e.tail e.head hblock
  have covers := cliqueExtend_cover_iff_of_closed hD ι hnatural θ e.tail e.head hbounds hclosed
  have hsource := cliqueRestrict_connected_of_block hD ι θ e.tail e.head hbounds hblock
  have hcoverθ : Cover (cliqueRestrict hD ι θ) 0 (Fin.last k) := by
    apply (covers _ 0 (Fin.last k)).mp
    rw [cliqueExtend_restrict]
    simpa only [Cover, θ.toUndecorated_selected] using hcθ
  have hcoverη : Cover (cliqueRestrict hD ι η) 0 (Fin.last k) := by
    apply (covers _ 0 (Fin.last k)).mp
    rw [cliqueExtend_eq_of_outside hD ι hnatural θ η houtside]
    simpa only [Cover, η.toUndecorated_selected] using hcη
  exact clique_lift_reachable hD ι hnatural θ η covers houtside
    (complete_reachable k _ _ hsource hcoverθ hη hcoverη htotal)

end VerticalStripLLT.Circular.DiagramProof

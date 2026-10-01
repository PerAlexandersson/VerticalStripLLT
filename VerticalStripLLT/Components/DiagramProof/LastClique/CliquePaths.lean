import VerticalStripLLT.Components.DiagramProof.LastClique.CompleteBlock
import VerticalStripLLT.Components.DiagramProof.Preparation.ReachabilityForcing

/-! Actual paths confined to one selected weak block of a natural clique. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {k n : ℕ} {D : Diagram n}

/-- A path in a selected complete block lifts to an actual ambient state with exact exterior. -/
theorem clique_lift_core_of_block (hD : Forward D) (e : Edge D.area)
    (ι : Fin (k + 1) ↪o Fin n) (hbounds : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head)
    (θ : Orientation D)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) ∧
        D.edgeData.selected θ.val x y) (ι 0) z)
    (α : Orientation (completeDiagram k))
    (hp : Relation.ReflTransGen (Flip (completeDiagram k)) (cliqueRestrict hD ι θ) α) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ u v, D.edgeData.selected η.val (ι u) (ι v) ↔
        (completeDiagram k).edgeData.selected α.val u v) ∧
      (∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
        (D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v)) := by
  have hnatural (a b : Fin (k + 1)) (hab : a < b) :
      ∃ f : Edge D.area, f.tail = ι a ∧ f.head = ι b :=
    exists_edge_of_orderEmbedding_mem_interval hD e ι hbounds hab
  exact clique_lift_core_reachable hD ι hnatural θ
    (cliqueExtend_cover_iff_of_closed hD ι hnatural θ e.tail e.head hbounds
      (selected_image_closed_of_block hD ι θ e.tail e.head hblock)) α hp

/-- Force reachability in a chosen selected clique block and restore its exterior. -/
theorem clique_exists_reachable_of_block (hD : Forward D) (e : Edge D.area)
    (ι : Fin (k + 1) ↪o Fin n) (hbounds : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head)
    (θ : Orientation D)
    (hblock : ∀ z, (∃ i, ι i = z) ↔ Relation.EqvGen
      (fun x y => (e.tail ≤ x ∧ x ≤ e.head) ∧ (e.tail ≤ y ∧ y ≤ e.head) ∧
        D.edgeData.selected θ.val x y) (ι 0) z)
    (u v : Fin (k + 1)) (huv : u ≤ v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.ReflTransGen (D.edgeData.selected η.val) (ι u) (ι v) ∧
      (∀ x y, (¬ ∃ a b, ι a = x ∧ ι b = y) →
        (D.edgeData.selected η.val x y ↔ D.edgeData.selected θ.val x y)) := by
  have hc := cliqueRestrict_connected_of_block hD ι θ e.tail e.head hbounds hblock
  obtain ⟨α, hp, huvα⟩ := exists_reachable_of_weakReach (complete_forward k)
    (cliqueRestrict hD ι θ) u v huv (hc u v)
  obtain ⟨η, hθη, hinside, houtside⟩ :=
    clique_lift_core_of_block hD e ι hbounds θ hblock α hp
  exact ⟨η, hθη, huvα.lift ι (fun a b h => (hinside a b).mpr h), houtside⟩

end VerticalStripLLT.Circular.DiagramProof

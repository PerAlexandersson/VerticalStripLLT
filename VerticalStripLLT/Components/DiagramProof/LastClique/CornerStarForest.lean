import VerticalStripLLT.Components.DiagramProof.Corners.CornerForest
import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueAnchorReplacement
import VerticalStripLLT.Components.DiagramProof.Foundation.EdgeSetGraph

/-! A retained corner forest with a star at a last corner. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

theorem isAcyclic_fromRel_of_forward_of_rightUnique
    {V : Type*} [LinearOrder V] {R : V → V → Prop}
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hright : Relator.RightUnique R) :
    (SimpleGraph.fromRel R).IsAcyclic := by
  let R' : OrderDual V → OrderDual V → Prop := fun u v => R v u
  have hforward' : ∀ ⦃u v : OrderDual V⦄, R' u v → u < v := by
    intro u v huv
    exact hforward huv
  have hleft' : Relator.LeftUnique R' := by
    intro u v w huv huw
    exact hright huv huw
  have h := isAcyclic_fromRel_of_forward_of_leftUnique hforward' hleft'
  have heq : SimpleGraph.fromRel R' = SimpleGraph.fromRel R := by
    ext u v
    change (u ≠ v ∧ (R v u ∨ R u v)) ↔ (u ≠ v ∧ (R u v ∨ R v u))
    exact and_congr_right (fun _ => or_comm)
  exact heq ▸ h

namespace CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

include hD

theorem corners_union_last_star_isAcyclic (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (S : Finset (Edge D.area))
    (hS : ∀ f ∈ S, g.tail < f.tail ∧ f.head = g.head) :
    (edgeSetGraph (F.edges ∪ S)).IsAcyclic := by
  let R : Fin n → Fin n → Prop := fun u v =>
    ∃ f ∈ F.edges ∪ S, f.tail = u ∧ f.head = v
  have hforward : ∀ ⦃u v⦄, R u v → u < v := by
    rintro u v ⟨f, _, rfl, rfl⟩
    exact hD f
  have hright : Relator.RightUnique R := by
    intro u v w huv huw
    rcases huv with ⟨f, hf, hfu, hfv⟩
    rcases huw with ⟨q, hq, hqu, hqw⟩
    rcases Finset.mem_union.mp hf with hfC | hfS
    · rcases Finset.mem_union.mp hq with hqC | hqS
      · apply F.step_rightUnique
        · exact (F.step_iff _ _).mpr ⟨f, hfC, hfu, hfv⟩
        · exact (F.step_iff _ _).mpr ⟨q, hqC, hqu, hqw⟩
      · have hft : f.tail ≤ g.tail := F.corner_tail_le_of_head_le hD hfC
          (hlast f.head)
        have hqt := (hS q hqS).1
        have hsame : q.tail = f.tail := hqu.trans hfu.symm
        exact (not_lt_of_ge hft (hsame ▸ hqt)).elim
    · rcases Finset.mem_union.mp hq with hqC | hqS
      · have hqt : q.tail ≤ g.tail := F.corner_tail_le_of_head_le hD hqC
          (hlast q.head)
        have hft := (hS f hfS).1
        have hsame : q.tail = f.tail := hqu.trans hfu.symm
        exact (not_lt_of_ge hqt (hsame.symm ▸ hft)).elim
      · exact hfv.symm.trans ((hS f hfS).2.trans ((hS q hqS).2.symm.trans hqw))
  change (SimpleGraph.fromRel R).IsAcyclic
  exact isAcyclic_fromRel_of_forward_of_rightUnique hforward hright

theorem corners_union_last_star_subset_goodEdges (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (S : Finset (Edge D.area))
    (hS : ∀ f ∈ S, g.tail < f.tail ∧ f.head = g.head) :
    F.edges ∪ S ⊆ F.goodEdges hD := by
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · exact (F.mem_goodEdges hD f).mpr (Or.inl hf)
  · exact (F.mem_goodEdges hD f).mpr
      (F.goodEdge_of_last_tail_lt hD g hlast (hS f hf).1)

/-- Extend the displayed corner chains and terminal star inside the good-edge graph. -/
theorem exists_tree_containing_corners_and_last_star (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (S : Finset (Edge D.area))
    (hS : ∀ f ∈ S, g.tail < f.tail ∧ f.head = g.head)
    (hconnected : (edgeSetGraph (F.goodEdges hD)).Connected) :
    ∃ T : SimpleGraph (Fin n), edgeSetGraph (F.edges ∪ S) ≤ T ∧
      T ≤ edgeSetGraph (F.goodEdges hD) ∧ T.IsTree :=
  hconnected.exists_isTree_le_of_le_of_isAcyclic
    (edgeSetGraph_mono (F.corners_union_last_star_subset_goodEdges hD g hlast S hS))
    (F.corners_union_last_star_isAcyclic hD g hlast S hS)

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof

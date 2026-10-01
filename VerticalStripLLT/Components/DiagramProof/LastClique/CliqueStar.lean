import VerticalStripLLT.Components.DiagramProof.Complete.Star
import VerticalStripLLT.Components.DiagramProof.LastClique.CliquePaths
import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueBlockReplacement
import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueAnchorReplacement
import VerticalStripLLT.Components.DiagramProof.LastClique.LastCornerRow

/-! A star at the last vertex inside the selected block containing the last corner. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {k n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- The last-corner block can be replaced by a star with extras and a pendant least vertex. -/
theorem exists_last_clique_block_star (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head) (ι : Fin (k + 1) ↪o Fin n)
    (hbounds : ∀ i, g.tail ≤ ι i ∧ ι i ≤ g.head)
    (hfirst : ι 0 = g.tail) (hfinal : ι (Fin.last k) = g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hblock : ∀ z, (∃ i, ι i = z) ↔
      Relation.EqvGen (cliqueBlockRelation g θ) (ι 0) z) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      (∀ i, ι i < g.head → D.edgeData.selected η.val (ι i) g.head) ∧
      (∀ x y, (¬ ∃ a b, ι a = x ∧ ι b = y) →
        (D.edgeData.selected η.val x y ↔ D.edgeData.selected θ.val x y)) ∧
      ∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y := by
  have hzero : (0 : Fin (k + 1)) < Fin.last k := by
    apply ι.lt_iff_lt.mp
    simpa only [hfirst, hfinal] using hD g
  have hk : 0 < k := hzero
  have hc := cliqueRestrict_connected_of_block hD ι θ g.tail g.head hbounds hblock
  have hrow (v : Fin (k + 1)) :
      (completeDiagram k).edgeData.selected (cliqueRestrict hD ι θ).val 0 v ↔
        v = Fin.last k := by
    rw [cliqueRestrict_selected, hfirst,
      F.anchor_selected_from_last_tail_iff hD θ hθ g hg hlast, ← hfinal]
    exact ι.injective.eq_iff
  obtain ⟨β, hβconn, hβcount, hβstar, hβrow, hβcover⟩ :=
    exists_complete_star k hk (cliqueRestrict hD ι θ) hc hrow
  have hp := complete_reachable k (cliqueRestrict hD ι θ) β hc
    (complete_cover_of_row k hk _ hrow) hβconn hβcover hβcount.symm
  obtain ⟨η, hθη, hinside, houtside⟩ :=
    clique_lift_core_of_block hD g ι hbounds θ hblock β hp
  refine ⟨η, hθη, ?_, ?_, houtside, ?_⟩
  · apply F.anchor_of_rows_le_last_tail hD g hlast θ η hθ
    intro u v hu
    by_cases himage : ∃ a b, ι a = u ∧ ι b = v
    · obtain ⟨a, b, ha, hb⟩ := himage
      have hu0 : u = g.tail := le_antisymm hu (by rw [← ha]; exact (hbounds a).1)
      have ha0 : a = 0 := ι.injective (ha.trans (hu0.trans hfirst.symm))
      subst a
      rw [← ha, ← hb, hinside, hβrow, ← hrow]
      exact cliqueRestrict_selected hD ι θ 0 b
    · exact houtside u v himage
  · intro i hi
    rw [← hfinal] at hi ⊢
    exact (hinside i (Fin.last k)).mpr (hβstar i (ι.lt_iff_lt.mp hi))
  · exact cliqueBlock_weakReach_iff g ι hbounds θ η hblock β hβconn hinside
      (fun x y h => (houtside x y h).symm)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

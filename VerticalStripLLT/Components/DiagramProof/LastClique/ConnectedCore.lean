import VerticalStripLLT.Components.DiagramProof.LastClique.CoreConnectivity
import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueBlockBounds
import VerticalStripLLT.Components.DiagramProof.LastClique.Preparation

/-! A prepared last clique has connected restriction to the retained core. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- The last-corner star and the other blocks' lower connections connect the retained core. -/
theorem selectedConnected_inducedRestrict_of_prepared_lastClique
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hconn : SelectedConnected θ)
    (hcorner : D.edgeData.selected θ.val g.tail g.head)
    (hstar : ∀ v, Relation.EqvGen (cliqueBlockRelation g θ) g.tail v → v < g.head →
      D.edgeData.selected θ.val v g.head)
    (hlower : ∀ x y, g.tail < x → x ≤ c →
      (¬ Relation.EqvGen (cliqueBlockRelation g θ) x g.tail) →
      Relation.EqvGen (cliqueBlockRelation g θ) x y → y ≤ c →
      Relation.EqvGen
        (fun a b => a ≤ c ∧ b ≤ c ∧ D.edgeData.selected θ.val a b) x y) :
    SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
      (inducedDiagram_naturalEdge_iff hD ι)
      (inducedDiagram_strictEndpoint_iff hD ι) θ) := by
  let α := inducedRestrict (inducedDiagram_forward hD ι) ι
    (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) θ
  obtain ⟨j, hj⟩ := (himage g.head).mpr (Or.inr rfl)
  have hhead : Relation.EqvGen (cliqueBlockRelation g θ) g.tail g.head :=
    .rel _ _ ⟨⟨le_rfl, (hD g).le⟩, ⟨(hD g).le, le_rfl⟩, hcorner⟩
  have hstarReach (u : Fin (k + 1))
      (hu : Relation.EqvGen (cliqueBlockRelation g θ) g.tail (ι u)) :
      WeakReach α u j := by
    by_cases hue : ι u = g.head
    · have huj : u = j := ι.injective (hue.trans hj.symm)
      subst u
      exact .refl _
    · apply Relation.EqvGen.rel
      apply (inducedRestrict_selected (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) θ u j).mpr
      rw [hj]
      exact hstar (ι u) hu (lt_of_le_of_ne (hlast _) hue)
  apply selectedConnected_inducedRestrict_of_lastClique_blocks
    hD ι c g hbefore himage θ hconn
  intro u v huv
  have hpath : Relation.EqvGen (cliqueBlockRelation g θ) (ι u) (ι v) := by
    exact Relation.EqvGen.mono
      (fun a b => (cliqueBlockRelation_iff_of_forward hD g θ a b).mpr) _ _ huv
  by_cases hu : Relation.EqvGen (cliqueBlockRelation g θ) g.tail (ι u)
  · exact .trans _ _ _ (hstarReach u hu)
      (.symm _ _ (hstarReach v (.trans _ _ _ hu hpath)))
  · have hv : ¬ Relation.EqvGen (cliqueBlockRelation g θ) g.tail (ι v) := by
      intro hv
      exact hu (.trans _ _ _ hv (.symm _ _ hpath))
    have huc : ι u ≤ c := ((himage (ι u)).mp ⟨u, rfl⟩).resolve_right
      (fun hue => hu (hue.symm ▸ hhead))
    have hvc : ι v ≤ c := ((himage (ι v)).mp ⟨v, rfl⟩).resolve_right
      (fun hve => hv (hve.symm ▸ hhead))
    rcases eqvGen_cliqueBlockRelation_eq_or_bounds g θ hpath with heq | hbounds
    · have huv : u = v := ι.injective heq
      subst v
      exact .refl _
    · have hau : g.tail < ι u := lt_of_le_of_ne hbounds.1.1 (by
        intro heq
        exact hu (heq ▸ Relation.EqvGen.refl _))
      exact weakReach_inducedRestrict_of_lower hD ι c
        (fun z hz => (himage z).mpr (Or.inl hz)) θ u v
        (hlower (ι u) (ι v) hau huc (fun h => hu (.symm _ _ h)) hpath hvc)

namespace CornerFamily

/-- A connected anchor reaches an anchor with connected retained core by actual flips. -/
theorem exists_reachable_connected_lastClique_core
    (F : CornerFamily D) (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (c : Fin n) (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ) (hconn : SelectedConnected θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι)
        (inducedDiagram_strictEndpoint_iff hD ι) η) ∧
      (∀ v, Relation.EqvGen (cliqueBlockRelation g θ) g.tail v → v < g.head →
        D.edgeData.selected η.val v g.head) ∧
      ∀ x y, Relation.EqvGen (cliqueBlockRelation g θ) x y ↔
        Relation.EqvGen (cliqueBlockRelation g η) x y := by
  obtain ⟨η, hp, hη, hstar, hlower, hpart⟩ :=
    F.exists_last_clique_preparation hD g hg hlast θ hθ c
  refine ⟨η, hp, hη, ?_, hstar, hpart⟩
  apply selectedConnected_inducedRestrict_of_prepared_lastClique hD ι c g
    hlast hbefore himage η ((selectedConnected_iff_of_reachable hp).mp hconn)
    ((mem_fullSelection_iff_selected η g).mp (hη.1 hg))
  · intro v hv
    exact hstar v ((hpart g.tail v).mpr hv)
  · intro x y hax hxc hsep hxy hyc
    exact hlower x y hax hxc (fun h => hsep ((hpart x g.tail).mp h))
      ((hpart x y).mpr hxy) hyc

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof

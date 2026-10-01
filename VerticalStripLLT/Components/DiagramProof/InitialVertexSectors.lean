import VerticalStripLLT.Components.DiagramProof.InitialVertexSectorWitness
import VerticalStripLLT.Components.DiagramProof.InitialVertexFeasibility
import VerticalStripLLT.Components.DiagramProof.InitialVertexSectorPaths
import VerticalStripLLT.Components.DiagramProof.SectorPaths

/-! Assemble the feasible initial-extra subsets using the actual crossing-slide paths. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

/-- All fixed-size anchors with connected initial cores connect through feasible extra sets. -/
theorem initialVertex_connected_core_anchors (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD (Fin.succOrderEmb (k + 1))),
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover α →
      (allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) α β)
    (hrem : ∀ e ∈ (allCorners D).initialVertexExtras hD f,
      ∀ d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area,
      (allCorners D).CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) →
      ((edgeSetGraph ((allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1)))).goodEdges
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))))).deleteEdges
          {s(d.tail, d.head)}).Connected)
    (θ τ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hτ : (allCorners D).Anchor hD τ)
    (hcθ : SelectedConnected (initialVertexRestrict hD θ))
    (hcτ : SelectedConnected (initialVertexRestrict hD τ))
    (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let ι := Fin.succOrderEmb (k + 1)
  let E := inducedDiagram hD ι
  let F := allCorners D
  let F' := allCorners E
  let J := F.initialVertexExtras hD f
  let m := (F'.goodEdges (inducedDiagram_forward hD ι)).card
  let s := totalSelected θ
  have hE := inducedDiagram_forward hD ι
  have hfF : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have hF' : F.induced hD ι = F' :=
    induced_allCorners_initialVertex hD f g hf hg hft hgt hfg
  have hnat : ∀ u v, Relation.EqvGen (naturalEdgeRelation (D := E)) u v := by
    intro u v
    apply Relation.EqvGen.mono ?_ u v (hcθ u v)
    rintro x y ⟨e, _, ht, hh⟩
    exact ⟨e, ht, hh⟩
  have hroom : k < m ∨ J = ∅ := by
    by_cases hJ : J = ∅
    · exact Or.inr hJ
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
      obtain ⟨het, _, hegood⟩ := F.initialVertex_extra_good hD f hfF hft e he
      obtain ⟨d, hlink, _, _, hdgood, _⟩ :=
        F.exists_initial_matching_core_edge hD f e hfF hft het hegood
      have hdG : d ∈ F'.goodEdges hE := by
        apply (F'.mem_goodEdges hE d).mpr
        change (F.induced hD ι).GoodEdge hE d at hdgood
        rw [hF'] at hdgood
        exact hdgood
      have hb := F'.goodEdges_card_lower_bound_of_delete_connected hE d hdG (hrem e he d hlink)
      left
      change k < (F'.goodEdges hE).card
      lia
  have feasible (σ : Orientation D) (hσ : F.Anchor hD σ)
      (hcσ : SelectedConnected (initialVertexRestrict hD σ))
      (hsσ : totalSelected σ = s) :
      selectedInitialVertexExtras σ f ⊆ J ∧ ∃ t, k ≤ t ∧ t ≤ m ∧
        t + 1 + (selectedInitialVertexExtras σ f).card = s := by
    have ha := initialVertex_anchor_restrict hD f g hf hg hft hgt hfg σ hσ
    have hl := connected_selected_card_lower_bound hE (by lia) _ hcσ
    have hu := Finset.card_le_card ((F'.anchor_iff_subsets hE _).mp ha).2
    have hcount := F.totalSelected_eq_initialVertex_core_add_one_add_extras
      hD σ hσ f hfF hft
    refine ⟨F.selectedInitialVertexExtras_subset hD σ hσ f,
      totalSelected (initialVertexRestrict hD σ), ?_, hu, ?_⟩
    · lia
    · exact hcount.symm.trans hsσ
  have witness (S : FeasibleSector J k m s) :
      ∃ σ : Orientation D, F.Anchor hD σ ∧
        SelectedConnected (initialVertexRestrict hD σ) ∧ totalSelected σ = s ∧
        selectedInitialVertexExtras σ f = S.val := by
    obtain ⟨t, hlt, hut, hts⟩ := S.property.2
    obtain ⟨α, hα, hcα, hsize⟩ := F'.exists_connected_anchor_card hE (by lia)
      hnat t (by lia) hut
    have hα' : (F.induced hD ι).Anchor hE α := by simpa only [hF'] using hα
    obtain ⟨σ, hσ, hcore, hrow⟩ :=
      F.exists_initialVertex_sector_witness hD f hfF hft S.val S.property.1 α hα'
    have hfS : f ∉ S.val := by
      intro h
      exact (Finset.mem_filter.mp (S.property.1 h)).2.2 rfl
    have hselected : selectedInitialVertexExtras σ f = S.val := by
      unfold selectedInitialVertexExtras
      rw [hrow]
      exact Finset.erase_insert hfS
    refine ⟨σ, hσ, hcore ▸ hcα, ?_, hselected⟩
    rw [F.totalSelected_eq_initialVertex_core_add_one_add_extras hD σ hσ f hfF hft,
      hcore, hselected, hsize]
    exact hts
  choose η hη hcη hsη heη using witness
  have deleted (S T : FeasibleSector J k m s) (e : Edge D.area)
      (he : e ∈ S.val) (hT : T.val = S.val.erase e) :
      Relation.ReflTransGen (Flip D) (η S) (η T) := by
    apply initialVertex_reachable_of_erase_extras hD f g hf hg hft hgt hfg hunique
      (η S) (η T) (hη S) (hη T) (hcη S) (hcη T) ((hsη S).trans (hsη T).symm) e
    · rw [heη S]
      exact he
    · rw [heη S, heη T]
      exact hT
    · exact hrem e (S.property.1 he)
  have step (S T : FeasibleSector J k m s) (h : feasibleSectorStep S T) :
      Relation.ReflTransGen (Flip D) (η S) (η T) := by
    rcases h with ⟨e, he, hT⟩ | ⟨e, he, hT⟩
    · apply flip_reachable_symm
      apply deleted T S e
      · rw [hT]
        exact Finset.mem_insert_self _ _
      · rw [hT]
        exact (Finset.erase_insert he).symm
    · exact deleted S T e he hT
  let S : FeasibleSector J k m s := ⟨_, feasible θ hθ hcθ rfl⟩
  let T : FeasibleSector J k m s := ⟨_, feasible τ hτ hcτ htotal.symm⟩
  have lift {U V : FeasibleSector J k m s}
      (hp : Relation.ReflTransGen feasibleSectorStep U V) :
      Relation.ReflTransGen (Flip D) (η U) (η V) := by
    induction hp with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.trans (step _ _ hstep)
  have middle := lift (feasibleSector_connected hroom S T)
  have same (σ : Orientation D) (hσ : F.Anchor hD σ)
      (hcσ : SelectedConnected (initialVertexRestrict hD σ))
      (hsσ : totalSelected σ = s) (U : FeasibleSector J k m s)
      (hex : selectedInitialVertexExtras σ f = U.val) :
      Relation.ReflTransGen (Flip D) σ (η U) := by
    apply initialVertex_reachable_of_same_initial_row hD f g hf hg hft hgt hfg hunique
      σ (η U) hσ (hη U) hcσ (hcη U) (hsσ.trans (hsη U).symm)
    apply initialVertex_selected_row_iff
    rw [F.row_eq_insert_selectedInitialVertexExtras hD σ hσ f hfF hft,
      F.row_eq_insert_selectedInitialVertexExtras hD (η U) (hη U) f hfF hft,
      hex, heη U]
  exact (same θ hθ hcθ rfl S rfl).trans
    (middle.trans (flip_reachable_symm (same τ hτ hcτ htotal.symm T rfl)))

end

end VerticalStripLLT.Circular.DiagramProof

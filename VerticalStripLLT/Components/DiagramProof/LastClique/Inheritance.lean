import VerticalStripLLT.Components.DiagramProof.LastClique.FixedEdges
import VerticalStripLLT.Components.DiagramProof.LastClique.CorePaths
import VerticalStripLLT.Components.DiagramProof.LastClique.ExtraPositions
import VerticalStripLLT.Components.DiagramProof.LastClique.SharedExchange
import VerticalStripLLT.Components.DiagramProof.LastClique.ExtraPositionPaths
import VerticalStripLLT.Components.DiagramProof.LastClique.CrossingCopies
import VerticalStripLLT.Components.DiagramProof.LastClique.SharedPosition

/-! Joining the two extra-position rearrangements in last-clique inheritance. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Fixed-edge anchors of equal size connect by the core and right-clique diagram paths. -/
theorem lastClique_fixed_anchors_connected
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g : Edge D.area) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hgc : g.tail < c) (hcg : c < g.head)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (A : Finset (Edge D.area)) (hFA : (allCorners D).edges ⊆ A)
    (hAcore : ∀ σ : Orientation D, A ⊆ fullSelection σ →
      SelectedConnected (inducedRestrict (inducedDiagram_forward hD ι) ι
        (inducedDiagram_naturalEdge_iff hD ι) (inducedDiagram_strictEndpoint_iff hD ι) σ))
    (hAstar : ∀ v, g.tail ≤ v → v < g.head → (edgeSetGraph A).Adj v g.head)
    (p q : Edge D.area) (hlink : (allCorners D).CopyLink p q)
    (hpgood : (allCorners D).terminal hD p.tail < (allCorners D).terminal hD p.head)
    (hpt : p.tail < g.tail) (hqt : g.tail < q.tail) (hqh : q.head = g.head)
    (hpA : p ∉ A) (hpcore : ∃ u v, ι u = p.tail ∧ ι v = p.head)
    (θ τ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hτ : (allCorners D).Anchor hD τ) (hAθ : A ⊆ fullSelection θ)
    (hAτ : A ⊆ fullSelection τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let F := allCorners D
  let P := F.goodEdges hD \ A
  let J := lastCliqueCoreExtraPositions ι P
  let K := lastCliqueRightExtraPositions g p P
  have hgm : g ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
  have hpP : p ∈ P := Finset.mem_sdiff.mpr
    ⟨(F.mem_goodEdges hD p).mpr (Or.inr hpgood), hpA⟩
  have hJ : J ⊆ P := Finset.filter_subset _ _
  have hK : K ⊆ P := Finset.insert_subset hpP (Finset.filter_subset _ _)
  have hcover : ∀ e ∈ P, e ∈ J ∨ e ∈ K := by
    intro e he
    have hcov := lastClique_extra_positions_cover hD ι c g p hbefore himage P hpP
    exact Finset.mem_union.mp (hcov ▸ he)
  have hoverlap : (J ∩ K).Nonempty :=
    ⟨p, lastClique_shared_extra_position ι g p P hpP hpcore⟩
  apply F.anchors_connected_of_overlapping_extra_positions hD A J K hJ hK hcover
    hoverlap ?_ θ τ hθ hτ hAθ hAτ htotal
  intro σ hσ hAσ e f hef he hf
  rcases hef with hcore | hright
  · have heP := Finset.mem_sdiff.mp (hJ hcore.1)
    have hfP := Finset.mem_sdiff.mp (hJ hcore.2)
    have hecore := (Finset.mem_filter.mp hcore.1).2
    have hfcore := (Finset.mem_filter.mp hcore.2).2
    obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hD σ hσ e f
      (fun heF => heP.2 (hFA heF)) ((F.mem_goodEdges hD f).mp hfP.1)
    have hAη : A ⊆ fullSelection η := by
      intro a ha
      rw [hfull]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨fun hae => heP.2 (hae ▸ ha), hAσ ha⟩)
    have hsize : totalSelected σ = totalSelected η := by
      rw [totalSelected, totalSelected, hfull,
        Finset.card_insert_of_notMem (fun h => hf (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem he]
      have hpos := Finset.card_pos.mpr ⟨e, he⟩
      lia
    have houtside (u v : Fin n) (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
        D.edgeData.selected σ.val u v ↔ D.edgeData.selected η.val u v := by
      have hne (r : Edge D.area) (hrt : r.tail = u) (hrh : r.head = v)
          (z : Edge D.area) (hz : ∃ a b, ι a = z.tail ∧ ι b = z.head) : r ≠ z := by
        rintro rfl
        obtain ⟨a, b, ha, hb⟩ := hz
        exact hout ⟨a, b, ha.trans hrt, hb.trans hrh⟩
      constructor
      · rintro ⟨r, hr, hrt, hrh⟩
        refine ⟨r, ?_, hrt, hrh⟩
        change r ∈ fullSelection η
        rw [hfull]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne r hrt hrh e hecore, hr⟩)
      · rintro ⟨r, hr, hrt, hrh⟩
        change r ∈ fullSelection η at hr
        rw [hfull] at hr
        exact ⟨r, (Finset.mem_erase.mp
          ((Finset.mem_insert.mp hr).resolve_left (hne r hrt hrh f hfcore))).2, hrt, hrh⟩
    exact ⟨η, lastClique_reachable_of_same_exterior hD ι c g hg hlast hgc hcg himage
      hcorners hunique σ η hσ hη (hAcore σ hAσ) (hAcore η hAη) hsize houtside, hη, hfull⟩
  · have hstarσ : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected σ.val v g.head := by
      intro v hav hve
      obtain ⟨r, hrt, hrh⟩ := exists_edge_of_naturalLift_of_le
        (D.naturalLift_of_tail_lt_head g (hD g)) hav hve le_rfl
      have hrA : r ∈ A := (edgeSetGraph_adj_iff_mem hD A r).mp (by
        rw [hrt, hrh]; exact hAstar v hav hve)
      have hs := (mem_fullSelection_iff_selected σ r).mp (hAσ hrA)
      simpa only [hrt, hrh] using hs
    obtain ⟨η, hp, hη, hfull, _⟩ := F.exists_last_clique_right_exchange hD g hgm hlast
      σ hσ hstarσ p q hlink hpgood hpt hqt hqh e f he hf
      (lastClique_right_extra_position_cases F hD g p hgm hlast A (hFA hgm) hAstar e
        hright.1)
      (lastClique_right_extra_position_cases F hD g p hgm hlast A (hFA hgm) hAstar f
        hright.2)
    exact ⟨η, hp, hη, hfull⟩

/-- Last-clique inheritance for connected anchors, with uniqueness assumed only in the core. -/
theorem anchors_connected_of_lastClique_core
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (f g : Edge D.area)
    (hf : IsCorner f) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hcross : f.tail < g.tail ∧ g.tail < f.head ∧ f.head < g.head)
    (hbefore : ∀ e : Edge D.area, IsCorner e → e ≠ g → e.head ≤ f.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ f.head ∨ z = g.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).Anchor hD θ)
    (hτ : (allCorners D).Anchor hD τ) (hcθ : SelectedConnected θ)
    (hcτ : SelectedConnected τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  let F := allCorners D
  have hfm : f ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have hgm : g ∈ F.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
  have hcorners : ∀ e : Edge D.area, IsCorner e →
      ∃ u v, ι u = e.tail ∧ ι v = e.head := by
    intro e he
    by_cases heg : e = g
    · subst e
      obtain ⟨u, hu⟩ := (himage g.tail).mpr (Or.inl hcross.2.1.le)
      obtain ⟨v, hv⟩ := (himage g.head).mpr (Or.inr rfl)
      exact ⟨u, v, hu, hv⟩
    · have hh := hbefore e he heg
      obtain ⟨u, hu⟩ := (himage e.tail).mpr (Or.inl ((hD e).le.trans hh))
      obtain ⟨v, hv⟩ := (himage e.head).mpr (Or.inl hh)
      exact ⟨u, v, hu, hv⟩
  obtain ⟨ξ, _, hξ, hcξ, _, _⟩ :=
    F.exists_reachable_connected_lastClique_core hD ι f.head g hgm hlast
      hbefore himage θ hθ hcθ
  obtain ⟨T, hT, hFT, hTG, hstar⟩ :=
    exists_lastClique_core_tree hD ι g hg hlast hcorners ξ hξ hcξ
  let A := lastCliqueFixedEdges hD ι f.head g T
  have hFA : F.edges ⊆ A := allCorners_subset_lastCliqueFixedEdges hD ι f.head g hcorners T hFT
  have hAstar := lastCliqueFixedEdges_star hD ι f.head g himage T hstar
  have hTG' : T ≤ edgeSetGraph (Finset.univ : Finset (Edge (inducedDiagram hD ι).area)) :=
    hTG.trans (edgeSetGraph_mono (Finset.subset_univ _))
  obtain ⟨p, q, hpt, hph, hqt, hqh, hlink, hpgood, _⟩ :=
    F.exists_crossing_copies hD f g hfm hgm hlast hcross
  have hpA : p ∉ A := crossing_shared_not_mem_lastCliqueFixedEdges hD ι f g p
    hfm hgm hpt hph hcross himage T hT.isAcyclic hFT hstar
  have hpcore : ∃ u v, ι u = p.tail ∧ ι v = p.head := by
    obtain ⟨u, hu⟩ := (himage f.tail).mpr (Or.inl (hD f).le)
    obtain ⟨v, hv⟩ := (himage g.tail).mpr (Or.inl hcross.2.1.le)
    exact ⟨u, v, hu.trans hpt.symm, hv.trans hph.symm⟩
  have hnormalize (σ : Orientation D) (hσ : F.Anchor hD σ) (hcσ : SelectedConnected σ) :
      ∃ η, Relation.ReflTransGen (Flip D) σ η ∧ F.Anchor hD η ∧ A ⊆ fullSelection η := by
    obtain ⟨η, hp, hη, hcore, hstarη⟩ := exists_reachable_lastClique_tree hD ι f.head g hg
      hlast hcross.2.1 hcross.2.2 hbefore himage hcorners hunique T hT hFT hTG hstar σ hσ hcσ
    exact ⟨η, hp, hη, lastCliqueFixedEdges_subset_selection hD ι f.head g hcross.2.1.le
      T η hcore hstarη⟩
  obtain ⟨α, hθα, hα, hAα⟩ := hnormalize θ hθ hcθ
  obtain ⟨β, hτβ, hβ, hAβ⟩ := hnormalize τ hτ hcτ
  have hsize : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hτβ))
  have hαβ := lastClique_fixed_anchors_connected hD ι f.head g hg hlast hcross.2.1
    hcross.2.2 hbefore himage hcorners hunique A hFA
    (fun σ hAσ => lastCliqueFixedEdges_connected_core hD ι f.head g T hT.connected hTG' σ hAσ)
    hAstar p q hlink hpgood (by simpa only [hpt] using hcross.1)
    (by simpa only [hqt] using hcross.2.1) hqh hpA hpcore α β hα hβ hAα hAβ hsize
  exact hθα.trans (hαβ.trans (flip_reachable_symm hτβ))

/-- Preparation extends the same last-clique inheritance to connected common-cover states. -/
theorem commonCover_connected_of_lastClique_core
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (f g : Edge D.area)
    (hf : IsCorner f) (hg : IsCorner g) (hlast : ∀ v : Fin n, v ≤ g.head)
    (hcross : f.tail < g.tail ∧ g.tail < f.head ∧ f.head < g.head)
    (hbefore : ∀ e : Edge D.area, IsCorner e → e ≠ g → e.head ≤ f.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ f.head ∨ z = g.head)
    (hunique : ∀ α β : Orientation (inducedDiagram hD ι),
      (allCorners (inducedDiagram hD ι)).CommonCover α →
      (allCorners (inducedDiagram hD ι)).CommonCover β →
      SelectedConnected α → SelectedConnected β → totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (inducedDiagram hD ι)) α β)
    (θ τ : Orientation D) (hθ : (allCorners D).CommonCover θ)
    (hτ : (allCorners D).CommonCover τ) (hcθ : SelectedConnected θ)
    (hcτ : SelectedConnected τ) (htotal : totalSelected θ = totalSelected τ) :
    Relation.ReflTransGen (Flip D) θ τ := by
  obtain ⟨α, hθα, hα, _⟩ := (allCorners D).exists_preparation hD θ hθ
  obtain ⟨β, hτβ, hβ, _⟩ := (allCorners D).exists_preparation hD τ hτ
  have hsize : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hτβ))
  have hp := anchors_connected_of_lastClique_core hD ι f g hf hg hlast hcross hbefore
    himage hunique α β hα hβ ((selectedConnected_iff_of_reachable hθα).mp hcθ)
    ((selectedConnected_iff_of_reachable hτβ).mp hcτ) hsize
  exact hθα.trans (hp.trans (flip_reachable_symm hτβ))

end

end VerticalStripLLT.Circular.DiagramProof

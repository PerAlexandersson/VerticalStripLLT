import VerticalStripLLT.Components.DiagramProof.TerminalClique
import VerticalStripLLT.Components.DiagramProof.ChainQuotient
import VerticalStripLLT.Components.DiagramProof.CompleteBlock
import VerticalStripLLT.Components.DiagramProof.CliqueCounts
import VerticalStripLLT.Components.DiagramProof.CliqueInterval
import VerticalStripLLT.Components.DiagramProof.PackedTerminalGraph
import VerticalStripLLT.Components.DiagramProof.OccupancyExchange

/-! Actual transfers between selected terminal copies in the last clique. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Connected selected terminal copies, together with the last corner, form
the whole selected interval block. -/
theorem last_clique_block_of_terminal_connected (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (A : Finset (Edge D.area)) (hAT : A ⊆ F.terminalEdges hforward)
    (hAS : A ⊆ fullSelection θ)
    (hconnected : (F.chainQuotient hforward A).Preconnected) (z : Fin n) :
    (c.tail ≤ z ∧ z ≤ c.head) ↔ Relation.EqvGen
      (fun x y => (c.tail ≤ x ∧ x ≤ c.head) ∧ (c.tail ≤ y ∧ y ≤ c.head) ∧
        D.edgeData.selected θ.val x y) c.tail z := by
  let R := fun x y => (c.tail ≤ x ∧ x ≤ c.head) ∧
    (c.tail ≤ y ∧ y ≤ c.head) ∧ D.edgeData.selected θ.val x y
  have terminal_bounds (v : Fin n) (hv : F.terminal hforward v = v) :
      c.tail ≤ v ∧ v ≤ c.head := ⟨(hv ▸ hterm v).le, hlast v⟩
  have hmap : ∀ B C : {t : Fin n // F.terminal hforward t = t},
      (F.chainQuotient hforward A).Reachable B C → Relation.EqvGen R B.val C.val := by
    intro B C h
    have hp := (eqvGen_iff_fromRel_reachable _ _).mpr h
    clear h
    induction hp with
    | rel B C hBC =>
      obtain ⟨e, he, ht, hh⟩ := hBC
      obtain ⟨het, heh⟩ := (F.mem_terminalEdges hforward e).mp (hAT he)
      have ht' : e.tail = B.val := het.symm.trans ht
      have hh' : e.head = C.val := heh.symm.trans hh
      exact Relation.EqvGen.rel _ _ ⟨terminal_bounds B.val B.property,
        terminal_bounds C.val C.property, e, hAS he, ht', hh'⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  constructor
  · rintro ⟨hz, _⟩
    rcases lt_or_eq_of_le hz with hlt | rfl
    · have hcT := F.terminal_eq_of_last_corner hforward c hlast (hforward c)
      have hzT := F.terminal_eq_of_last_corner hforward c hlast hlt
      have hcz : Relation.EqvGen R c.head z :=
        hmap ⟨c.head, hcT⟩ ⟨z, hzT⟩ (hconnected _ _)
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _ ⟨⟨le_rfl, (hforward c).le⟩,
          ⟨(hforward c).le, le_rfl⟩, c, hθ.1 hc, rfl, rfl⟩) hcz
    · exact Relation.EqvGen.refl _
  · intro h
    have hclosed : ∀ x y, Relation.EqvGen R x y →
        ((c.tail ≤ x ∧ x ≤ c.head) ↔ c.tail ≤ y ∧ y ≤ c.head) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (hclosed _ _ h).mp ⟨le_rfl, (hforward c).le⟩

/-- Exchange two terminal copies when both selected terminal graphs are connected.
The endpoint has exactly the prescribed swap, including every exterior edge. -/
theorem exists_terminal_exchange (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ : Orientation D) (hθ : F.Anchor hforward θ) (e f : Edge D.area)
    (heT : e ∈ F.terminalEdges hforward) (hfT : f ∈ F.terminalEdges hforward)
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (hsource : (F.chainQuotient hforward
      (fullSelection θ ∩ F.terminalEdges hforward)).Preconnected)
    (htarget : (F.chainQuotient hforward
      (insert f ((fullSelection θ).erase e) ∩ F.terminalEdges hforward)).Preconnected) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  classical
  obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hforward θ hθ e f
    (F.terminalEdge_good_not_corner hforward heT).2
    ((F.mem_goodEdges hforward f).mp (F.terminalEdge_good_not_corner hforward hfT).1)
  obtain ⟨k, ι, hlo, hhi, himage⟩ :=
    exists_interval_orderEmbedding c.tail c.head (hforward c).le
  have hbounds (i) := (himage (ι i)).mp ⟨i, rfl⟩
  have hnatural (i j) (hij : i < j) :
      ∃ g : Edge D.area, g.tail = ι i ∧ g.head = ι j :=
    exists_edge_of_orderEmbedding_mem_interval hforward c ι hbounds hij
  have hinside (g : Edge D.area) (hg : g ∈ F.terminalEdges hforward) :
      cliqueEdgeInImage (D := D) ι g := by
    obtain ⟨hgt, hgh⟩ := (F.mem_terminalEdges hforward g).mp hg
    obtain ⟨i, hi⟩ := (himage g.tail).mpr ⟨(hgt ▸ hterm g.tail).le, hlast _⟩
    obtain ⟨j, hj⟩ := (himage g.head).mpr ⟨(hgh ▸ hterm g.head).le, hlast _⟩
    exact ⟨i, j, hi, hj⟩
  have heinside := hinside e heT
  have hfinside := hinside f hfT
  have hblock (σ : Orientation D) (hσ : F.Anchor hforward σ)
      (hconn : (F.chainQuotient hforward
        (fullSelection σ ∩ F.terminalEdges hforward)).Preconnected) (z) :
      (∃ i, ι i = z) ↔ Relation.EqvGen
        (fun x y => (c.tail ≤ x ∧ x ≤ c.head) ∧ (c.tail ≤ y ∧ y ≤ c.head) ∧
          D.edgeData.selected σ.val x y) (ι 0) z := by
    rw [hlo, himage]
    exact F.last_clique_block_of_terminal_connected hforward c hc hlast hterm σ hσ _
      Finset.inter_subset_right Finset.inter_subset_left hconn z
  have htarget' : (F.chainQuotient hforward
      (fullSelection η ∩ F.terminalEdges hforward)).Preconnected := by
    rw [hfull]
    exact htarget
  have houtside (u v : Fin n) (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
      D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v := by
    have hne (g : Edge D.area) (ht : g.tail = u) (hh : g.head = v)
        (p : Edge D.area) (hp : cliqueEdgeInImage (D := D) ι p) : g ≠ p := by
      rintro rfl
      obtain ⟨a, b, ha, hb⟩ := hp
      exact hout ⟨a, b, ha.trans ht, hb.trans hh⟩
    constructor
    · rintro ⟨g, hg, ht, hh⟩
      refine ⟨g, ?_, ht, hh⟩
      change g ∈ fullSelection η
      rw [hfull]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne g ht hh e heinside, hg⟩)
    · rintro ⟨g, hg, ht, hh⟩
      change g ∈ fullSelection η at hg
      rw [hfull] at hg
      exact ⟨g, (Finset.mem_erase.mp
        ((Finset.mem_insert.mp hg).resolve_left (hne g ht hh f hfinside))).2, ht, hh⟩
  refine ⟨η, ?_, hη, hfull⟩
  apply clique_reachable_of_block hforward c ι hbounds θ η (hblock θ hθ hsource)
  · exact cliqueRestrict_connected_of_block hforward ι η c.tail c.head hbounds
      (hblock η hη htarget')
  · rw [hlo, hhi]
    exact F.commonCover_of_anchor hforward hθ c hc
  · rw [hlo, hhi]
    exact F.commonCover_of_anchor hforward hη c hc
  · exact cliqueRestrict_totalSelected_swap hforward ι hnatural θ η e f
      hfull he hf heinside hfinside
  · exact houtside

/-- The two graph conditions for a direct transfer give an actual flip path
and the exact unit change of occupancies. -/
theorem exists_direct_terminal_transfer (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ : Orientation D) (hθ : F.Anchor hforward θ) (e f : Edge D.area)
    (heT : e ∈ F.terminalEdges hforward) (hfT : f ∈ F.terminalEdges hforward)
    (hef : e ≠ f) (he : 0 < F.occupancy hforward θ (F.copyLabel hforward e))
    (hf : F.occupancy hforward θ (F.copyLabel hforward f) <
      ((F.goodEdges hforward).filter
        (fun g => F.copyLabel hforward g = F.copyLabel hforward f)).card)
    (hsource : ((F.chainQuotient hforward (fullSelection θ)).deleteEdges
      {s(F.chainVertex hforward f.tail, F.chainVertex hforward f.head)}).Preconnected)
    (htarget : ((F.chainQuotient hforward (fullSelection θ)).deleteEdges
      {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)} ⊔
      SimpleGraph.edge (F.chainVertex hforward f.tail)
        (F.chainVertex hforward f.head)).Preconnected) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      ∀ p, F.occupancy hforward η p =
        if p = F.copyLabel hforward e then F.occupancy hforward θ p - 1
        else if p = F.copyLabel hforward f then F.occupancy hforward θ p + 1
        else F.occupancy hforward θ p := by
  classical
  obtain ⟨σ, hσ, hθσ, hcounts, hpacked⟩ :=
    F.exists_terminal_packing hforward θ hθ f hfT hf
  have heσ : e ∈ fullSelection σ := (hpacked e heT).mpr ⟨he, hef⟩
  have hfσ : f ∉ fullSelection σ := fun h => ((hpacked f hfT).mp h).2 rfl
  have hgraph := F.packed_terminal_graph_eq hforward c
    (fun v => ⟨hterm v, hlast _⟩) θ hθ σ f hfT hpacked
  have hsource' : (F.chainQuotient hforward
      (fullSelection σ ∩ F.terminalEdges hforward)).Preconnected := by
    rw [hgraph]
    exact hsource
  have htarget' : (F.chainQuotient hforward
      (insert f ((fullSelection σ).erase e) ∩ F.terminalEdges hforward)).Preconnected := by
    have hset : insert f ((fullSelection σ).erase e) ∩ F.terminalEdges hforward =
        insert f ((fullSelection σ ∩ F.terminalEdges hforward).erase e) := by
      ext g
      by_cases hgf : g = f
      · subst g
        simp [hfT]
      · simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, hgf, false_or]
        tauto
    rw [hset, F.chainQuotient_terminal_insert_erase hforward _
      Finset.inter_subset_right e f heT, hgraph, deleteEdges_deleteEdges_sup_edge]
    exact htarget
  obtain ⟨η, hση, hη, hfull⟩ := F.exists_terminal_exchange hforward c hc hlast hterm
    σ hσ e f heT hfT heσ hfσ hsource' htarget'
  refine ⟨η, hθσ.trans hση, hη, ?_⟩
  intro p
  have hlabel : F.copyLabel hforward e ≠ F.copyLabel hforward f := fun h =>
    hef (F.terminalEdges_label_injective hforward heT hfT h)
  rw [F.occupancy_of_fullSelection_exchange hforward σ η e f hfull heσ hfσ hlabel p]
  simp only [hcounts]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

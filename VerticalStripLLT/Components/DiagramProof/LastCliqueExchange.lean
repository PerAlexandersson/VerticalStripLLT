import VerticalStripLLT.Components.DiagramProof.CliqueBlockBounds
import VerticalStripLLT.Components.DiagramProof.CliqueCounts
import VerticalStripLLT.Components.DiagramProof.CliquePaths
import VerticalStripLLT.Components.DiagramProof.CliqueInterval
import VerticalStripLLT.Components.DiagramProof.CornerChains
import VerticalStripLLT.Components.DiagramProof.LastCliqueStarRepair
import VerticalStripLLT.Components.DiagramProof.ParallelMoves
import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! Actual exchange paths for two selected positions inside a last clique. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- An exact exchange inside a connected clique lifts with its entire exterior restored. -/
theorem clique_reachable_of_exchange (g : Edge D.area) (hg : g ∈ F.edges)
    (θ η : Orientation D) (hθ : F.Anchor hD θ) (hη : F.Anchor hD η)
    (e f : Edge D.area) (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (hef : fullSelection η = insert f ((fullSelection θ).erase e))
    (heinside : g.tail ≤ e.tail ∧ e.head ≤ g.head)
    (hfinside : g.tail ≤ f.tail ∧ f.head ≤ g.head)
    (hsource : ∀ v, g.tail ≤ v → v ≤ g.head →
      Relation.EqvGen (cliqueBlockRelation g θ) g.tail v)
    (htarget : ∀ v, g.tail ≤ v → v ≤ g.head →
      Relation.EqvGen (cliqueBlockRelation g η) g.tail v) :
    Relation.ReflTransGen (Flip D) θ η := by
  obtain ⟨k, ι, hlo, hhi, himage⟩ :=
    exists_interval_orderEmbedding g.tail g.head (hD g).le
  have hbounds : ∀ i, g.tail ≤ ι i ∧ ι i ≤ g.head := by
    intro i
    exact (himage (ι i)).mp ⟨i, rfl⟩
  have hnatural (i j) (hij : i < j) :
      ∃ q : Edge D.area, q.tail = ι i ∧ q.head = ι j :=
    exists_edge_of_orderEmbedding_mem_interval hD g ι hbounds hij
  have hblock (σ : Orientation D)
      (hreach : ∀ v, g.tail ≤ v → v ≤ g.head →
        Relation.EqvGen (cliqueBlockRelation g σ) g.tail v) (z : Fin n) :
      (∃ i, ι i = z) ↔
        Relation.EqvGen (cliqueBlockRelation g σ) (ι 0) z := by
    constructor
    · intro hz
      obtain ⟨i, rfl⟩ := hz
      rw [hlo]
      exact hreach _ (hbounds i).1 (hbounds i).2
    · intro hz
      rcases eqvGen_cliqueBlockRelation_eq_or_bounds g σ hz with hEq | hbounds'
      · have hzbound : g.tail ≤ z ∧ z ≤ g.head := by
          rw [← hEq]
          exact hbounds 0
        exact (himage _).mpr hzbound
      · exact (himage _).mpr hbounds'.2
  have hsource' := hblock θ hsource
  have htarget' := hblock η htarget
  have heimage : ∃ i j, ι i = e.tail ∧ ι j = e.head := by
    obtain ⟨i, hi⟩ := (himage e.tail).mpr
      ⟨heinside.1, (hD e).le.trans heinside.2⟩
    obtain ⟨j, hj⟩ := (himage e.head).mpr
      ⟨heinside.1.trans (hD e).le, heinside.2⟩
    exact ⟨i, j, hi, hj⟩
  have hfimage : ∃ i j, ι i = f.tail ∧ ι j = f.head := by
    obtain ⟨i, hi⟩ := (himage f.tail).mpr
      ⟨hfinside.1, (hD f).le.trans hfinside.2⟩
    obtain ⟨j, hj⟩ := (himage f.head).mpr
      ⟨hfinside.1.trans (hD f).le, hfinside.2⟩
    exact ⟨i, j, hi, hj⟩
  have hηconn : SelectedConnected (cliqueRestrict hD ι η) := by
    exact cliqueRestrict_connected_of_block hD ι η g.tail g.head hbounds htarget'
  have houtside (u v : Fin n) (hout : ¬ ∃ a b, ι a = u ∧ ι b = v) :
      D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v := by
    have hne (q : Edge D.area) (ht : q.tail = u) (hh : q.head = v)
        (p : Edge D.area) (hp : ∃ a b, ι a = p.tail ∧ ι b = p.head) : q ≠ p := by
      rintro rfl
      obtain ⟨a, b, ha, hb⟩ := hp
      exact hout ⟨a, b, ha.trans ht, hb.trans hh⟩
    constructor
    · rintro ⟨q, hq, ht, hh⟩
      refine ⟨q, ?_, ht, hh⟩
      change q ∈ fullSelection η
      rw [hef]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne q ht hh e
        heimage, hq⟩)
    · rintro ⟨q, hq, ht, hh⟩
      change q ∈ fullSelection η at hq
      rw [hef] at hq
      exact ⟨q, (Finset.mem_erase.mp
        ((Finset.mem_insert.mp hq).resolve_left
          (hne q ht hh f hfimage))).2, ht, hh⟩
  have hcount := cliqueRestrict_totalSelected_swap hD ι hnatural θ η e f hef he hf
    heimage hfimage
  have hcoverθ : Cover θ (ι 0) (ι (Fin.last k)) := by
    rw [hlo, hhi]
    exact F.commonCover_of_anchor hD hθ g hg
  have hcoverη : Cover η (ι 0) (ι (Fin.last k)) := by
    rw [hlo, hhi]
    exact F.commonCover_of_anchor hD hη g hg
  exact clique_reachable_of_block hD g ι hbounds θ η
    hsource' hηconn hcoverθ hcoverη hcount houtside

/-- Ordinary extra edges in the last clique exchange with the entire terminal star
selected at both endpoints, and every other selected edge restored exactly. -/
theorem exists_last_clique_extra_exchange (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (e f : Edge D.area) (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (hae : g.tail < e.tail) (hee : e.head < g.head)
    (haf : g.tail < f.tail) (hfe : f.head < g.head) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  have hen : e ∉ F.edges := by
    intro he
    exact (not_le_of_gt hae) (F.corner_tail_le_of_head_le hD (f := g) he (hlast _))
  have hfgood : F.GoodEdge hD f := by
    right
    rw [F.terminal_eq_of_last_corner hD g hlast haf,
      F.terminal_eq_of_last_corner hD g hlast (haf.trans (hD f))]
    exact hD f
  obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hD θ hθ e f hen hfgood
  have hstarη : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
    intro v hav hve
    exact selected_of_exchange_of_ne θ η e f hfull (Or.inr hee.ne') (hstar v hav hve)
  refine ⟨η, ?_, hη, hfull, hstarη⟩
  exact F.clique_reachable_of_exchange hD g hg θ η hθ hη e f he hf hfull
    ⟨hae.le, hee.le⟩ ⟨haf.le, hfe.le⟩
    (cliqueBlock_connected_of_terminal_star hD g θ hstar)
    (cliqueBlock_connected_of_terminal_star hD g η hstarη)

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

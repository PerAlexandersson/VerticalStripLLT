import VerticalStripLLT.Components.DiagramProof.LastClique.StarExchange

/-! The shared-position exchange using a single temporary edge in the last clique. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- Replace ce inside the clique and then slide ba to ce, restoring the terminal star. -/
theorem exists_shared_exchange_of_clique_join
    (g : Edge D.area) (hg : g ∈ F.edges) (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (p q : Edge D.area) (hlink : F.CopyLink p q)
    (hpgood : F.terminal hD p.tail < F.terminal hD p.head)
    (hpt : p.tail < g.tail) (hqt : g.tail < q.tail) (hqh : q.head = g.head)
    (hp : p ∈ fullSelection θ)
    (x : Edge D.area) (hx : g.tail < x.tail) (hxh : x.head < g.head)
    (hxabsent : x ∉ fullSelection θ) (r : Edge D.area) (d : Fin n)
    (hgd : g.tail < d) (hdg : d < g.head) (hdq : d ≠ q.tail)
    (hr : r ∈ insert x ((fullSelection θ).erase q))
    (hrend : (r.tail = q.tail ∧ r.head = d) ∨ (r.tail = d ∧ r.head = q.tail)) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert x ((fullSelection θ).erase p) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  have hpq : p ≠ q := fun heq => (hpt.trans hqt).ne (congrArg Edge.tail heq)
  have hqx : q ≠ x := by
    intro heq
    exact hxh.ne ((congrArg Edge.head heq).symm.trans hqh)
  have hq : q ∈ fullSelection θ := (mem_fullSelection_iff_selected θ q).mpr (by
    rw [hqh]
    exact hstar q.tail hqt.le (by simpa only [← hqh] using hD q))
  obtain ⟨σ, hθσ, hσ, hσfull⟩ := F.exists_last_clique_star_exchange hD g hg hlast
    θ hθ hstar q.tail q rfl hqh hqt x hx hxh hxabsent r d hgd hdg hdq hr hrend
  have hpσ : p ∈ fullSelection σ := by
    rw [hσfull]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hpq, hp⟩)
  have hqσ : q ∉ fullSelection σ := by
    rw [hσfull]
    simp [hqx]
  obtain ⟨η, hση, hη, hηfull⟩ :=
    F.exists_forwardCopyExchange hD σ hσ p q hlink hpgood hpσ hqσ
  have hfull : fullSelection η = insert x ((fullSelection θ).erase p) := by
    rw [hηfull, hσfull]
    ext e
    simp only [Finset.mem_insert, Finset.mem_erase]
    grind
  refine ⟨η, hθσ.trans hση, hη, hfull, ?_⟩
  intro v hav hve
  have hphead : p.head < g.head := by
    have h := hlink.2.2.trans (hD q)
    simpa only [hqh] using h
  exact selected_of_exchange_of_ne θ η p x hfull (Or.inr hphead.ne') (hstar v hav hve)

/-- The one-temporary-edge repair exchanges the shared copy for any absent clique extra.
All other selected edges, including the endpoint tree, are restored exactly. -/
theorem exists_last_clique_shared_exchange
    (g : Edge D.area) (hg : g ∈ F.edges) (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (p q : Edge D.area) (hlink : F.CopyLink p q)
    (hpgood : F.terminal hD p.tail < F.terminal hD p.head)
    (hpt : p.tail < g.tail) (hqt : g.tail < q.tail) (hqh : q.head = g.head)
    (hp : p ∈ fullSelection θ)
    (x : Edge D.area) (hx : g.tail < x.tail) (hxh : x.head < g.head)
    (hxabsent : x ∉ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert x ((fullSelection θ).erase p) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  have hc : q.tail < g.head := by simpa only [← hqh] using hD q
  obtain ⟨d, had, hde, hdc⟩ : ∃ d : Fin n, g.tail < d ∧ d < g.head ∧ d ≠ q.tail := by
    by_cases hxt : x.tail = q.tail
    · exact ⟨x.head, hx.trans (hD x), hxh, by simpa only [← hxt] using (hD x).ne'⟩
    · exact ⟨x.tail, hx, (hD x).trans hxh, hxt⟩
  obtain ⟨r, hrend⟩ : ∃ r : Edge D.area,
      (r.tail = q.tail ∧ r.head = d) ∨ (r.tail = d ∧ r.head = q.tail) := by
    rcases lt_or_gt_of_ne hdc with hdc | hcd
    · obtain ⟨r, hrt, hrh⟩ := exists_edge_of_naturalLift_of_le
        (D.naturalLift_of_tail_lt_head g (hD g)) had.le hdc hc.le
      exact ⟨r, Or.inr ⟨hrt, hrh⟩⟩
    · obtain ⟨r, hrt, hrh⟩ := exists_edge_of_naturalLift_of_le
        (D.naturalLift_of_tail_lt_head g (hD g)) hqt.le hcd hde.le
      exact ⟨r, Or.inl ⟨hrt, hrh⟩⟩
  have har : g.tail < r.tail := by
    rcases hrend with h | h
    · simpa only [h.1] using hqt
    · simpa only [h.1] using had
  have hre : r.head < g.head := by
    rcases hrend with h | h
    · simpa only [h.2] using hde
    · simpa only [h.2] using hc
  have hrq : r ≠ q := by
    intro heq
    exact hre.ne ((congrArg Edge.head heq).trans hqh)
  by_cases hr : r ∈ fullSelection θ
  · exact F.exists_shared_exchange_of_clique_join hD g hg hlast θ hθ hstar p q
      hlink hpgood hpt hqt hqh hp x hx hxh hxabsent r d had hde hdc
      (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hrq, hr⟩)) hrend
  · obtain ⟨σ, hpσ, hσ, hσfull, hσstar⟩ :=
      F.exists_shared_exchange_of_clique_join hD g hg hlast θ hθ hstar p q
        hlink hpgood hpt hqt hqh hp r har hre hr r d had hde hdc
        (Finset.mem_insert_self _ _) hrend
    by_cases hrx : r = x
    · exact ⟨σ, hpσ, hσ, by simpa only [hrx] using hσfull, hσstar⟩
    have hrσ : r ∈ fullSelection σ := by rw [hσfull]; exact Finset.mem_insert_self _ _
    have hxσ : x ∉ fullSelection σ := by
      rw [hσfull]
      simp [Ne.symm hrx, hxabsent]
    obtain ⟨η, hση, hη, hηfull, hηstar⟩ := F.exists_last_clique_extra_exchange hD
      g hg hlast σ hσ hσstar r x hrσ hxσ har hre hx hxh
    refine ⟨η, hpσ.trans hση, hη, ?_, hηstar⟩
    rw [hηfull, hσfull]
    ext e
    simp only [Finset.mem_insert, Finset.mem_erase]
    grind

/-- Reverse the same diagram path to exchange a clique extra for the shared copy. -/
theorem exists_last_clique_reverse_shared_exchange
    (g : Edge D.area) (hg : g ∈ F.edges) (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (p q : Edge D.area) (hlink : F.CopyLink p q)
    (hpgood : F.terminal hD p.tail < F.terminal hD p.head)
    (hpt : p.tail < g.tail) (hqt : g.tail < q.tail) (hqh : q.head = g.head)
    (hp : p ∉ fullSelection θ)
    (x : Edge D.area) (hx : g.tail < x.tail) (hxh : x.head < g.head)
    (hxsel : x ∈ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert p ((fullSelection θ).erase x) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  have hxn : x ∉ F.edges := by
    intro h
    exact (not_le_of_gt hx) (F.corner_tail_le_of_head_le hD (f := g) h (hlast _))
  have hxp : x ≠ p := fun h => hp (h ▸ hxsel)
  obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hD θ hθ x p hxn (Or.inr hpgood)
  have hstarη : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
    intro v hav hve
    exact selected_of_exchange_of_ne θ η x p hfull (Or.inr hxh.ne') (hstar v hav hve)
  have hpη : p ∈ fullSelection η := by rw [hfull]; exact Finset.mem_insert_self _ _
  have hxη : x ∉ fullSelection η := by rw [hfull]; simp [hxp]
  obtain ⟨ζ, hηζ, _, hζfull, _⟩ := F.exists_last_clique_shared_exchange hD g hg hlast
    η hη hstarη p q hlink hpgood hpt hqt hqh hpη x hx hxh hxη
  have hζθ : ζ = θ := by
    apply fullSelection_injective
    rw [hζfull, hfull]
    ext e
    simp only [Finset.mem_insert, Finset.mem_erase]
    grind
  subst ζ
  exact ⟨η, flip_reachable_symm hηζ, hη, hfull, hstarη⟩

/-- All exact exchanges in the restricted right pool use only clique paths and the slide.
The pool consists of internal extra edges and the single shared copy. -/
theorem exists_last_clique_right_exchange
    (g : Edge D.area) (hg : g ∈ F.edges) (hlast : ∀ v : Fin n, v ≤ g.head)
    (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (p q : Edge D.area) (hlink : F.CopyLink p q)
    (hpgood : F.terminal hD p.tail < F.terminal hD p.head)
    (hpt : p.tail < g.tail) (hqt : g.tail < q.tail) (hqh : q.head = g.head)
    (e f : Edge D.area) (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (hepool : e = p ∨ g.tail < e.tail ∧ e.head < g.head)
    (hfpool : f = p ∨ g.tail < f.tail ∧ f.head < g.head) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) ∧
      ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected η.val v g.head := by
  rcases hepool with heq | hepool
  · subst e
    rcases hfpool with hfq | hfpool
    · exact (hf (hfq.symm ▸ he)).elim
    · exact F.exists_last_clique_shared_exchange hD g hg hlast θ hθ hstar p q hlink
        hpgood hpt hqt hqh he f hfpool.1 hfpool.2 hf
  · rcases hfpool with hfq | hfpool
    · subst f
      exact F.exists_last_clique_reverse_shared_exchange hD g hg hlast θ hθ hstar p q
        hlink hpgood hpt hqt hqh hf e hepool.1 hepool.2 he
    · exact F.exists_last_clique_extra_exchange hD g hg hlast θ hθ hstar e f he hf
        hepool.1 hepool.2 hfpool.1 hfpool.2

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

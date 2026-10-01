import VerticalStripLLT.Components.DiagramProof.LastCliqueExchange

/-! Exchange one terminal-star edge for an ordinary last-clique position. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

theorem exists_last_clique_star_exchange (g : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head) (θ : Orientation D) (hθ : F.Anchor hD θ)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head)
    (c : Fin n) (q : Edge D.area) (hqt : q.tail = c) (hqh : q.head = g.head)
    (hgc : g.tail < c) (x : Edge D.area) (hx : g.tail < x.tail) (hxh : x.head < g.head)
    (hxabsent : x ∉ fullSelection θ) (r : Edge D.area) (d : Fin n)
    (hgd : g.tail < d) (hdg : d < g.head) (hdq : d ≠ q.tail)
    (hr : r ∈ insert x ((fullSelection θ).erase q))
    (hrend : (r.tail = q.tail ∧ r.head = d) ∨ (r.tail = d ∧ r.head = q.tail)) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      fullSelection η = insert x ((fullSelection θ).erase q) := by
  have hqnot : q ∉ F.edges := by
    intro hq
    have hle := F.corner_tail_le_of_head_le hD hq (f := g) (by rw [hqh])
    exact (not_le_of_gt hgc) (by simpa only [hqt] using hle)
  have hxgood : F.GoodEdge hD x := by
    right
    rw [F.terminal_eq_of_last_corner hD g hlast hx,
      F.terminal_eq_of_last_corner hD g hlast (hx.trans (hD x))]
    exact hD x
  have hqsel : q ∈ fullSelection θ := by
    apply (mem_fullSelection_iff_selected θ q).mpr
    rw [hqt, hqh]
    exact hstar c hgc.le (by simpa only [hqt, hqh] using hD q)
  obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hD θ hθ q x hqnot hxgood
  have hcorner : D.edgeData.selected η.val g.tail g.head := by
    apply selected_of_exchange_of_ne θ η q x hfull
      (Or.inl (by simpa only [hqt] using hgc.ne))
    exact (mem_fullSelection_iff_selected θ g).mp (hθ.1 hg)
  have hstarη : ∀ v, g.tail < v → v < g.head → v ≠ c →
      D.edgeData.selected η.val v g.head := by
    intro v hgv hvg hvc
    apply selected_of_exchange_of_ne θ η q x hfull
    left
    simpa only [hqt] using hvc
    exact hstar v hgv.le hvg
  have hrη : D.edgeData.selected η.val r.tail r.head := by
    apply (mem_fullSelection_iff_selected η r).mp
    rw [hfull]
    exact hr
  have hjoin : Relation.EqvGen (cliqueBlockRelation g η) c d := by
    rcases hrend with ⟨hrt, hrh⟩ | ⟨hrt, hrh⟩
    · apply Relation.EqvGen.rel _ _
      apply (cliqueBlockRelation_iff_of_forward hD g η c d).mpr
      exact ⟨hgc.le, hdg.le, by simpa only [hrt, hrh, hqt] using hrη⟩
    · apply Relation.EqvGen.symm _ _
      apply Relation.EqvGen.rel _ _
      apply (cliqueBlockRelation_iff_of_forward hD g η d c).mpr
      exact ⟨hgd.le, (by simpa only [hqt, hqh] using (hD q).le),
        by simpa only [hrt, hrh, hqt] using hrη⟩
  have htarget := cliqueBlock_connected_of_repaired_star hD g η c d hgd hdg
    (by simpa only [hqt] using hdq) hcorner hstarη hjoin
  have hsource := cliqueBlock_connected_of_terminal_star hD g θ hstar
  refine ⟨η, ?_, hη, hfull⟩
  apply F.clique_reachable_of_exchange hD g hg θ η hθ hη q x hqsel hxabsent hfull
  · exact ⟨by simpa only [hqt] using hgc.le,
      hqh.le⟩
  · exact ⟨hx.le, hxh.le⟩
  · exact hsource
  · exact htarget

end

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof

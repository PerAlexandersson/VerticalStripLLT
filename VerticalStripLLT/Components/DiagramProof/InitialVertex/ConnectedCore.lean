import VerticalStripLLT.Components.DiagramProof.InitialVertex.Restriction
import VerticalStripLLT.Components.DiagramProof.InitialVertex.Copies
import VerticalStripLLT.Components.DiagramProof.InitialVertex.Connectivity
import VerticalStripLLT.Components.DiagramProof.Preparation.ParallelMoves

/-! Crossing slides connect the core after deleting the initial vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

namespace CornerFamily

/-- A selected edge from zero into a different core block has a vacant matching core edge. -/
theorem exists_initial_core_join (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (θ : Orientation D) (hθ : F.Anchor hD θ) (hc : SelectedConnected θ)
    (hnot : ¬ SelectedConnected (initialVertexRestrict hD θ)) :
    ∃ e q : Edge D.area, e ∈ fullSelection θ ∧ e.tail = 0 ∧ q.tail ≠ 0 ∧
      F.CopyLink e q ∧ F.terminal hD e.tail < F.terminal hD e.head ∧
      q ∉ fullSelection θ := by
  have hfh : f.head ≠ 0 := ne_of_gt (by simpa only [hft] using hD f)
  obtain ⟨a, ha⟩ := Fin.eq_succ_of_ne_zero hfh
  obtain ⟨v, hv, hno⟩ := exists_initial_vertex_obstruction hD θ
    (initialVertexRestrict hD θ) (initialVertexRestrict_selected hD θ) hc a hnot
  obtain ⟨e, he, het, heh⟩ := hv
  change e.tail = 0 at het
  change e.head = v.succ at heh
  have hen : e ∉ F.edges := by
    intro heF
    have hhead : e.head = f.head := F.step_rightUnique
      ((F.step_iff _ _).mpr ⟨e, heF, rfl, rfl⟩)
      ((F.step_iff _ _).mpr ⟨f, hf, hft.trans het.symm, rfl⟩)
    have hav : a = v := Fin.succ_inj.mp (ha.symm.trans (hhead.symm.trans heh))
    apply hno
    rw [hav]
    exact Relation.EqvGen.refl _
  have hegood : F.terminal hD e.tail < F.terminal hD e.head :=
    (hθ.2 e he).resolve_left hen
  obtain ⟨q, hqt, hlink, _, _, _, _, _⟩ :=
    F.exists_initial_matching_edge hD f e hf (het.trans hft.symm) hegood
  have hqn : q.tail ≠ 0 := hqt.symm ▸ hfh
  refine ⟨e, q, he, het, hqn, hlink, hegood, ?_⟩
  intro hq
  have hqh : q.head ≠ 0 := ne_of_gt
    ((Fin.pos_iff_ne_zero.mpr hqn).trans (hD q))
  obtain ⟨w, hw⟩ := Fin.eq_succ_of_ne_zero hqh
  have haq : (inducedDiagram hD (Fin.succOrderEmb (k + 1))).edgeData.selected
      (initialVertexRestrict hD θ).val a w := by
    apply (initialVertexRestrict_selected hD θ a w).mpr
    have hs := (mem_fullSelection_iff_selected θ q).mp hq
    simpa only [hqt, ha, hw] using hs
  have hvw : (inducedDiagram hD (Fin.succOrderEmb (k + 1))).edgeData.selected
      (initialVertexRestrict hD θ).val v w := by
    apply (initialVertexRestrict_selected hD θ v w).mpr
    obtain ⟨c, hcF, hct, hch⟩ := (F.step_iff e.head q.head).mp hlink.2.1
    have hs := (mem_fullSelection_iff_selected θ c).mp (hθ.1 hcF)
    simpa only [hct, hch, heh, hw] using hs
  exact hno (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ haq)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hvw)))

/-- Repeatedly slide one extra edge at zero into the core until the core is connected. -/
theorem exists_reachable_connected_initialVertex_core (F : CornerFamily D) (hD : Forward D)
    (f : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (θ : Orientation D) (hθ : F.Anchor hD θ) (hc : SelectedConnected θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hD η ∧
      SelectedConnected (initialVertexRestrict hD η) := by
  generalize hN : ((fullSelection θ).filter (fun e => e.tail = 0)).card = N
  induction N using Nat.strong_induction_on generalizing θ with
  | h N ih =>
    by_cases hcore : SelectedConnected (initialVertexRestrict hD θ)
    · exact ⟨θ, Relation.ReflTransGen.refl, hθ, hcore⟩
    · obtain ⟨e, q, he, het, hqt, hlink, hegood, hq⟩ :=
        F.exists_initial_core_join hD f hf hft θ hθ hc hcore
      obtain ⟨ζ, hp, hζ, hfull⟩ :=
        F.exists_forwardCopyExchange hD θ hθ e q hlink hegood he hq
      have hfilter : (fullSelection ζ).filter (fun d => d.tail = 0) =
          ((fullSelection θ).filter (fun d => d.tail = 0)).erase e := by
        ext d
        rw [hfull]
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hd | hd, hz⟩
          · exact (hqt (hd ▸ hz)).elim
          · exact ⟨hd.1, hd.2, hz⟩
        · rintro ⟨hne, hs, hz⟩
          exact ⟨Or.inr ⟨hne, hs⟩, hz⟩
      have hless : ((fullSelection ζ).filter (fun d => d.tail = 0)).card < N := by
        rw [hfilter, ← hN]
        exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨he, het⟩)
      obtain ⟨η, hpη, hη, hcη⟩ := ih _ hless ζ hζ
        ((selectedConnected_iff_of_reachable hp).mp hc) rfl
      exact ⟨η, hp.trans hpη, hη, hcη⟩

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof

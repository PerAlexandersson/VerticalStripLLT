import VerticalStripLLT.Components.DiagramProof.Preparation.ChildMerge
import VerticalStripLLT.Components.DiagramProof.Preparation.ChildMergeCovers
import VerticalStripLLT.Components.DiagramProof.Preparation.CoverReachability
import VerticalStripLLT.Components.DiagramProof.Preparation.ParallelMoves

/-! Merge all children of the greatest vertex into its greatest proper child. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Repeating the four-flip move leaves only `z` and `j` covering the greatest vertex `t`. -/
theorem exists_merge_other_children (hforward : Forward D) (θ : Orientation D)
    (z j t : Fin n) (hz : ∀ v, z ≤ v) (hjt : j < t)
    (ht : ∀ v, v ≤ t) (hj : ∀ v, v < t → v ≤ j)
    (hunique : Relator.RightUnique (Cover θ)) (hchild : Cover θ j t)
    (hrowz : ∀ v, D.edgeData.selected θ.val z v ↔ v = t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relator.RightUnique (Cover η) ∧ Cover η j t ∧
      (∀ v, D.edgeData.selected η.val z v ↔ v = t) ∧
      ∀ i, Cover η i t → i = z ∨ i = j := by
  classical
  let count (σ : Orientation D) := ((fullSelection σ).filter (fun e => e.head = t)).card
  generalize hN : count θ = N
  induction N using Nat.strong_induction_on generalizing θ with
  | h N ih =>
    by_cases hdone : ∀ i, Cover θ i t → i = z ∨ i = j
    · exact ⟨θ, Relation.ReflTransGen.refl, hunique, hchild, hrowz, hdone⟩
    push Not at hdone
    obtain ⟨i, hitCover, hiz, hij⟩ := hdone
    have hzi : z < i := lt_of_le_of_ne (hz i) hiz.symm
    have hijlt : i < j := lt_of_le_of_ne (hj i hitCover.1) hij
    have hrowi := selected_iff_eq_top_of_cover hforward hunique hitCover ht
    have hrowj := selected_iff_eq_top_of_cover hforward hunique hchild ht
    obtain ⟨α, hθα, hα⟩ := exists_childMerge hforward θ z i j t hzi hijlt hjt
      hrowz hrowi hrowj
    have huniqueα : Relator.RightUnique (Cover α) :=
      relationCover_rightUnique_after_child_merge
        (fun {_ _} hs => θ.selected_lt_of_forward hforward hs)
        hunique hijlt hitCover hchild hα
    have hrowzα : ∀ v, D.edgeData.selected α.val z v ↔ v = t := by
      intro v
      rw [hα]
      simp [hzi.ne, hrowz v]
    have hrowjα : ∀ v, D.edgeData.selected α.val j v ↔ v = t := by
      intro v
      rw [hα]
      simp [hij.symm, hrowj v]
    have hchildα : Cover α j t := relationCover_of_first_outgoing
      (fun {_ _} hs => α.selected_lt_of_forward hforward hs) ((hrowjα t).mpr rfl) (by
        intro v _ hvt hv
        exact hvt.ne ((hrowjα v).mp hv))
    obtain ⟨e, he, het, heh⟩ := (hrowi t).mpr rfl
    obtain ⟨f, _, hft, hfh⟩ := (hα i j).mpr (Or.inl ⟨rfl, rfl⟩)
    change e.tail = i at het
    change e.head = t at heh
    change f.tail = i at hft
    change f.head = j at hfh
    have hfull : fullSelection α = insert f ((fullSelection θ).erase e) := by
      apply fullSelection_eq_of_exchange e f
      intro u v
      simpa only [exchangeRelation, het, heh, hft, hfh] using hα u v
    have hfilter : (fullSelection α).filter (fun g => g.head = t) =
        ((fullSelection θ).filter (fun g => g.head = t)).erase e := by
      rw [hfull]
      ext g
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      have hfne : f.head ≠ t := fun h => hjt.ne (hfh.symm.trans h)
      grind
    have hmeasure : count α < N := by
      rw [← hN]
      change ((fullSelection α).filter (fun g => g.head = t)).card <
        ((fullSelection θ).filter (fun g => g.head = t)).card
      rw [hfilter]
      exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨he, heh⟩)
    obtain ⟨η, hαη, hηunique, hηchild, hηrow, hηdone⟩ :=
      ih _ hmeasure α huniqueα hchildα hrowzα rfl
    exact ⟨η, hθα.trans hαη, hηunique, hηchild, hηrow, hηdone⟩

/-- After merging the children, moving `jt` to `zj` makes every vertex below `t`
reach `j` inside that prefix. -/
theorem exists_move_last_child (hforward : Forward D) (θ : Orientation D)
    (z j t : Fin n) (hz : ∀ v, z ≤ v) (hzj : z < j) (hjt : j < t)
    (ht : ∀ v, v ≤ t)
    (hunique : Relator.RightUnique (Cover θ)) (hconnected : SelectedConnected θ)
    (hchild : Cover θ j t) (hrowz : ∀ v, D.edgeData.selected θ.val z v ↔ v = t)
    (hchildren : ∀ i, Cover θ i t → i = z ∨ i = j) :
    ∃ η : Orientation D, Flip D θ η ∧ Cover η z j ∧ Cover η z t ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = z ∧ v = j) ∨ (D.edgeData.selected θ.val u v ∧ ¬ (u = j ∧ v = t))) ∧
      ∀ v, v ≤ j → Relation.ReflTransGen (D.edgeData.selected η.val) v j := by
  have hzt : Cover θ z t := relationCover_of_first_outgoing
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) ((hrowz t).mpr rfl) (by
      intro v _ hvt hv
      exact hvt.ne ((hrowz v).mp hv))
  obtain ⟨η, hθη, hztη, hzjη, hη⟩ :=
    exists_incomingSwap_of_covers hforward θ z j t hchild hzt hzj
  refine ⟨η, hθη, hzjη, hztη, hη, ?_⟩
  intro v hvj
  by_cases hvz : v = z
  · subst v
    exact Relation.ReflTransGen.single ((hη z j).mpr (Or.inl ⟨rfl, rfl⟩))
  have hp := relationCover_reachable
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs)
    (reachable_top_of_connected_of_rightUnique_covers hforward hunique hconnected t ht v)
  have hvjPath : Relation.ReflTransGen (D.edgeData.selected θ.val) v j := by
    rcases hp.cases_tail with heq | ⟨w, hvw, hwt⟩
    · have hvt : v < t := hvj.trans_lt hjt
      exact (hvt.ne heq.symm).elim
    · rcases hchildren w hwt with hwz | hwj
      · have hvwle := reachable_le (fun {_ _} h => h.1) hvw
        rw [hwz] at hvwle
        exact (hvz (le_antisymm hvwle (hz v))).elim
      · subst w
        exact reachable_of_relationCover_path
          (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hvw
  apply reachable_mono_on_interval
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) (lo := v) (hi := j)
      ?_ hvjPath le_rfl le_rfl
  intro a b _ hbj hab
  apply (hη a b).mpr
  refine Or.inr ⟨hab, ?_⟩
  rintro ⟨_, rfl⟩
  exact not_le_of_gt hjt hbj

end VerticalStripLLT.Circular.DiagramProof

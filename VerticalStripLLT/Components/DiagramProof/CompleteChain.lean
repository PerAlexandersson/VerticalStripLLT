import VerticalStripLLT.Components.DiagramProof.CompleteRestriction
import VerticalStripLLT.Components.DiagramProof.CompletePrefix
import VerticalStripLLT.Components.DiagramProof.CornerTransport

/-! The recursive chain construction in a complete diagram. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Every connected state covering the extreme corner reaches a state containing
`0n,12,23,...,(n-1)n`, with `0n` its only edge out of `0`. -/
theorem exists_complete_chain (n : ℕ) (θ : Orientation (completeDiagram (n + 1)))
    (hcover : Cover θ 0 (Fin.last (n + 1))) (hconnected : SelectedConnected θ) :
    ∃ η : Orientation (completeDiagram (n + 1)),
      Relation.ReflTransGen (Flip (completeDiagram (n + 1))) θ η ∧
      (∀ v, (completeDiagram (n + 1)).edgeData.selected η.val 0 v ↔
        v = Fin.last (n + 1)) ∧
      ∀ u v : Fin (n + 2), 0 < u → u.val + 1 = v.val →
        (completeDiagram (n + 1)).edgeData.selected η.val u v := by
  induction n with
  | zero =>
    refine ⟨θ, Relation.ReflTransGen.refl, ?_, ?_⟩
    · intro v
      constructor
      · intro hv
        have hlt := θ.selected_lt_of_forward (complete_forward 1) hv
        apply Fin.ext
        have hvlt := v.isLt
        change v.val = 1
        change 0 < v.val at hlt
        lia
      · rintro rfl
        exact selected_of_cover (complete_forward 1) hcover
    · intro u v hu huv
      have hv := v.isLt
      change 0 < u.val at hu
      lia
  | succ n ih =>
    let D := completeDiagram (n + 2)
    let z : Fin (n + 3) := 0
    let j : Fin (n + 3) := (Fin.last (n + 1)).castSucc
    let t : Fin (n + 3) := Fin.last (n + 2)
    let F := allCorners D
    have hF : F.edges = {completeCornerEdge (n + 2) (by lia)} :=
      complete_maximalCorners (n + 2) (by lia)
    have hC : F.CommonCover θ := by
      intro e he
      rw [hF] at he
      have heq := Finset.mem_singleton.mp he
      subst e
      simpa using hcover
    have hzj : z < j := by change 0 < n + 1; lia
    have hjt : j < t := by change n + 1 < n + 2; lia
    obtain ⟨β, hθβ, hzjβ, hztβ, hrowβ, hjtβ, hprefixβ⟩ :=
      F.exists_connected_prefix_of_single_corner (complete_forward (n + 2)) θ hC
        hconnected hF (completeCornerEdge_tail _ _) (completeCornerEdge_head _ _)
        (fun v => Fin.zero_le v) (fun v => Fin.le_last v) hzj hjt
        (by intro v hv; change v.val ≤ n + 1; change v.val < n + 2 at hv; lia)
    have hcoreCover : Cover (completeRestrict β) 0 (Fin.last (n + 1)) :=
      (completeRestrict_cover_iff β _ _).mpr hzjβ
    have hcoreConnected : SelectedConnected (completeRestrict β) :=
      completeRestrict_connected β (fun v => hprefixβ v.castSucc (Fin.le_last v))
    obtain ⟨α, hβα, hrowα, hchainα⟩ := ih (completeRestrict β) hcoreCover hcoreConnected
    let γ := completeExtend β α
    have hβγ : Relation.ReflTransGen (Flip D) β γ := complete_lift_reachable β hβα
    have hrowγ (v : Fin (n + 3)) : D.edgeData.selected γ.val z v ↔ v = j ∨ v = t := by
      change (completeDiagram (n + 2)).edgeData.selected (completeExtend β α).val 0 v ↔ _
      rw [completeExtend_selected]
      constructor
      · rintro (⟨a, b, ha, hb, hab⟩ | ⟨hv, _⟩)
        · have ha0 : a = 0 := Fin.ext (congrArg (fun x : Fin (n + 3) => x.val) ha)
          subst a
          have hbtop := (hrowα b).mp hab
          exact Or.inl (hb.symm.trans (congrArg Fin.castSucc hbtop))
        · exact Or.inr hv
      · rintro (rfl | rfl)
        · exact Or.inl ⟨0, Fin.last (n + 1), rfl, rfl, (hrowα _).mpr rfl⟩
        · exact Or.inr ⟨rfl, (hrowβ t).mpr (Or.inr rfl)⟩
    have hsinkj : ∀ v, ¬ D.edgeData.selected γ.val j v := by
      intro v h
      have hjv := γ.selected_lt_of_forward (complete_forward (n + 2)) h
      have hv : v = t := by
        apply Fin.ext
        have hbound := v.isLt
        change n + 1 < v.val at hjv
        change v.val = n + 2
        lia
      subst v
      exact hjtβ ((completeExtend_top β α j).mp h)
    have hsinkt : ∀ v, ¬ D.edgeData.selected γ.val t v := by
      intro v h
      exact (not_lt_of_ge (Fin.le_last v))
        (γ.selected_lt_of_forward (complete_forward (n + 2)) h)
    have hcoverj : Cover γ z j := by
      apply relationCover_of_other_sinks
        (fun {_ _} h => γ.selected_lt_of_forward (complete_forward (n + 2)) h)
        ((hrowγ j).mpr (Or.inl rfl))
      intro w hw hne
      rcases (hrowγ w).mp hw with rfl | rfl
      · exact (hne rfl).elim
      · exact hsinkt
    have hcovert : Cover γ z t := by
      apply relationCover_of_other_sinks
        (fun {_ _} h => γ.selected_lt_of_forward (complete_forward (n + 2)) h)
        ((hrowγ t).mpr (Or.inr rfl))
      intro w hw hne
      rcases (hrowγ w).mp hw with rfl | rfl
      · exact hsinkj
      · exact (hne rfl).elim
    obtain ⟨η, hγη, _, _, hη⟩ :=
      exists_outgoingSwap_of_covers (complete_forward (n + 2)) γ z j t
        hcoverj hcovert hjt
    refine ⟨η, (hθβ.trans hβγ).tail hγη, ?_, ?_⟩
    · intro v
      rw [hη]
      change (z = j ∧ v = t) ∨ (D.edgeData.selected γ.val z v ∧
        ¬ (z = z ∧ v = j)) ↔ v = t
      rw [hrowγ]
      simp only [hzj.ne, false_and, false_or, true_and]
      have hne := hjt.ne
      grind
    · intro u v hu huv
      rw [hη]
      by_cases hv : v = t
      · have huj : u = j := by
          apply Fin.ext
          change u.val = n + 1
          have hvt : v.val = n + 2 := congrArg Fin.val hv
          lia
        exact Or.inl ⟨huj, hv⟩
      · have hvlt : v.val < n + 2 := by
          have hb := v.isLt
          have hne : v.val ≠ n + 2 := fun h => hv (Fin.ext h)
          lia
        have hult : u.val < n + 2 := by lia
        let u' : Fin (n + 2) := ⟨u.val, hult⟩
        let v' : Fin (n + 2) := ⟨v.val, hvlt⟩
        have hsel := (completeExtend_inside β α u' v').mpr (hchainα u' v' hu huv)
        exact Or.inr ⟨hsel, fun h => (ne_of_gt hu) h.1⟩

/-- The chain path also exists with the extreme corner kept strict at every state. -/
theorem exists_complete_chain_marked (n : ℕ)
    (θ : Orientation (completeCornerDiagram (n + 1) (Nat.succ_pos n)))
    (hcover : Cover θ 0 (Fin.last (n + 1))) (hconnected : SelectedConnected θ) :
    ∃ η : Orientation (completeCornerDiagram (n + 1) (Nat.succ_pos n)),
      Relation.ReflTransGen
          (Flip (completeCornerDiagram (n + 1) (Nat.succ_pos n))) θ η ∧
      (∀ v,
        (completeCornerDiagram (n + 1) (Nat.succ_pos n)).edgeData.selected η.val 0 v ↔
          v = Fin.last (n + 1)) ∧
      ∀ u v : Fin (n + 2), 0 < u → u.val + 1 = v.val →
        (completeCornerDiagram (n + 1) (Nat.succ_pos n)).edgeData.selected η.val u v := by
  let U := completeDiagram (n + 1)
  let e := completeCornerEdge (n + 1) (Nat.succ_pos n)
  let he := completeCornerEdge_isCorner (n + 1) (Nat.succ_pos n)
  let θ₀ : Orientation U := θ.toUndecorated
  have hrelθ : U.edgeData.selected θ₀.val =
      (completeCornerDiagram (n + 1) (Nat.succ_pos n)).edgeData.selected θ.val :=
    θ.toUndecorated_selected
  have hcover₀ : Cover θ₀ 0 (Fin.last (n + 1)) := by
    simpa only [Cover, hrelθ] using hcover
  have hconnected₀ : SelectedConnected θ₀ := by
    simpa only [SelectedConnected, WeakReach, hrelθ] using hconnected
  have heθ₀ : e ∈ fullSelection θ₀ := by
    apply (mem_fullSelection_iff_selected θ₀ e).mpr
    simpa only [e, completeCornerEdge_tail, completeCornerEdge_head] using
      selected_of_cover (complete_forward (n + 1)) hcover₀
  obtain ⟨η₀, hp, hrow, hchain⟩ := exists_complete_chain n θ₀ hcover₀ hconnected₀
  have heη₀ : e ∈ fullSelection η₀ := (corner_mem_iff_of_reachable hp he).mp heθ₀
  let η := markCorner (complete_forward (n + 1)) η₀ e he heη₀
  have hpMarked := (reachable_markCorner_iff (D := U) (complete_forward (n + 1))
    e he heθ₀ heη₀).mpr hp
  have hstart : markCorner (complete_forward (n + 1)) θ₀ e he heθ₀ = θ := by
    apply fullSelection_injective
    exact (fullSelection_markCorner (complete_forward (n + 1)) θ₀ e he heθ₀).trans
      (Finset.empty_union (fullSelection θ))
  refine ⟨η, ?_, ?_, ?_⟩
  · rw [hstart] at hpMarked
    exact hpMarked
  · intro v
    exact (selected_markCorner_iff (complete_forward (n + 1)) η₀ e he heη₀ 0 v).trans
      (hrow v)
  · intro u v hu huv
    exact (selected_markCorner_iff (complete_forward (n + 1)) η₀ e he heη₀ u v).mpr
      (hchain u v hu huv)

end

end VerticalStripLLT.Circular.DiagramProof

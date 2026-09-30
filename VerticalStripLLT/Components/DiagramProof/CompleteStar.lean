import VerticalStripLLT.Components.DiagramProof.CompleteConnectivity
import VerticalStripLLT.Components.DiagramProof.EdgeSetGraph
import VerticalStripLLT.Components.DiagramProof.HassePaths

/-! A fixed star endpoint at each connected size in a complete diagram. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

def completeStarEdges (k : ℕ) : Finset (Edge (completeDiagram k).area) :=
  Finset.univ.image fun v : Fin k =>
    completeEdge k v.castSucc (Fin.last k) v.castSucc_lt_last

theorem completeStarEdges_card (k : ℕ) : (completeStarEdges k).card = k := by
  unfold completeStarEdges
  calc
    _ = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_of_injective _ (by
        intro u v huv
        have htail := congrArg Edge.tail huv
        apply Fin.castSucc_injective _
        simpa only [completeEdge_tail] using htail)
    _ = k := by simp only [Finset.card_univ, Fintype.card_fin]

theorem complete_cover_of_row (k : ℕ) (hk : 0 < k)
    (β : Orientation (completeDiagram k))
    (hβrow : ∀ v, (completeDiagram k).edgeData.selected β.val 0 v ↔ v = Fin.last k) :
    Cover β 0 (Fin.last k) := by
  refine ⟨?_, Relation.ReflTransGen.single ((hβrow _).mpr rfl), ?_⟩
  · change 0 < k
    exact hk
  intro w h0w hwlast ⟨hreach, _⟩
  rcases hreach.cases_head with h | ⟨x, h0x, hxw⟩
  · exact h0w.ne h
  · have hxlast := (hβrow x).mp h0x
    subst x
    have hle := reachable_le
      (fun {_ _} h => β.selected_lt_of_forward (complete_forward k) h) hxw
    exact (not_le_of_gt hwlast) hle

theorem exists_complete_star (k : ℕ) (hk : 0 < k) (θ : Orientation (completeDiagram k))
    (hconnected : SelectedConnected θ)
    (hrow : ∀ v, (completeDiagram k).edgeData.selected θ.val 0 v ↔ v = Fin.last k) :
    ∃ β : Orientation (completeDiagram k), SelectedConnected β ∧
      totalSelected β = totalSelected θ ∧
      (∀ v, v < Fin.last k →
        (completeDiagram k).edgeData.selected β.val v (Fin.last k)) ∧
      (∀ v, (completeDiagram k).edgeData.selected β.val 0 v ↔ v = Fin.last k) ∧
      Cover β 0 (Fin.last k) := by
  let star := completeStarEdges k
  let allowed : Finset (Edge (completeDiagram k).area) :=
    Finset.univ.filter fun e => e.tail ≠ 0 ∨ e.head = Fin.last k
  have hstar_allowed : star ⊆ allowed := by
    intro e he
    change e ∈ completeStarEdges k at he
    unfold completeStarEdges at he
    rcases Finset.mem_image.mp he with ⟨v, _, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
    exact completeEdge_head k v.castSucc (Fin.last k) v.castSucc_lt_last
  have hθallowed : fullSelection θ ⊆ allowed := by
    intro e he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases hzero : e.tail = 0
    · right
      apply (hrow e.head).mp
      have hselected := (mem_fullSelection_iff_selected θ e).mp he
      simpa only [hzero] using hselected
    · exact Or.inl hzero
  have hgraph : (edgeSetGraph (fullSelection θ)).Connected := by
    refine ⟨?_⟩
    intro u v
    exact (eqvGen_iff_fromRel_reachable u v).mp (hconnected u v)
  have hsource_lower : k ≤ (fullSelection θ).card := by
    have hcard := hgraph.card_vert_le_card_edgeSet_add_one
    rw [edgeSetGraph_card (complete_forward k), Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    lia
  have hstar_lower : star.card ≤ (fullSelection θ).card := by
    simpa only [star, completeStarEdges_card] using hsource_lower
  obtain ⟨A, hstarA, hAallowed, hAcard⟩ :=
    Finset.exists_subsuperset_card_eq hstar_allowed hstar_lower
      (Finset.card_le_card hθallowed)
  let β : Orientation (completeDiagram k) :=
    ofFullSelection (complete_forward k) A (by simp)
  have hβfull : fullSelection β = A := fullSelection_ofFullSelection ..
  have hstar_selected (v : Fin k) :
      (completeDiagram k).edgeData.selected β.val v.castSucc (Fin.last k) := by
    let e := completeEdge k v.castSucc (Fin.last k) v.castSucc_lt_last
    have he : e ∈ fullSelection β := by
      rw [hβfull]
      apply hstarA
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
    simpa only [e, completeEdge_tail, completeEdge_head] using
      (mem_fullSelection_iff_selected β e).mp he
  have hβrow (v : Fin (k + 1)) :
      (completeDiagram k).edgeData.selected β.val 0 v ↔ v = Fin.last k := by
    constructor
    · rintro ⟨e, he, ht, hh⟩
      change e ∈ fullSelection β at he
      rw [hβfull] at he
      rcases Finset.mem_filter.mp (hAallowed he) with ⟨_, hallowed⟩
      rcases hallowed with htail | hhead
      · exact (htail (ht.trans rfl)).elim
      · exact hh.symm.trans hhead
    · rintro rfl
      let v : Fin k := ⟨0, hk⟩
      have hv0 : v.castSucc = (0 : Fin (k + 1)) := by
        apply Fin.ext
        rfl
      simpa only [hv0] using hstar_selected v
  have hβconnected : SelectedConnected β := by
    intro u v
    change Relation.EqvGen ((completeDiagram k).edgeData.selected β.val) u v
    have hto : Relation.EqvGen ((completeDiagram k).edgeData.selected β.val) u
        (Fin.last k) := by
      rcases Fin.eq_castSucc_or_eq_last u with ⟨x, rfl⟩ | rfl
      · exact Relation.EqvGen.rel _ _ (hstar_selected x)
      · exact Relation.EqvGen.refl _
    have hfrom : Relation.EqvGen ((completeDiagram k).edgeData.selected β.val)
        (Fin.last k) v := by
      rcases Fin.eq_castSucc_or_eq_last v with ⟨x, rfl⟩ | rfl
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hstar_selected x))
      · exact Relation.EqvGen.refl _
    exact Relation.EqvGen.trans _ _ _ hto hfrom
  have hβcover := complete_cover_of_row k hk β hβrow
  refine ⟨β, hβconnected, ?_, ?_, hβrow, hβcover⟩
  · rw [totalSelected, hβfull]
    exact hAcard
  · intro v hv
    obtain ⟨x, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hv)
    exact hstar_selected x

end

end VerticalStripLLT.Circular.DiagramProof

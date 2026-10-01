import VerticalStripLLT.Components.DiagramProof.Complete.Opening
import VerticalStripLLT.Components.DiagramProof.Preparation.ChildMerge
import VerticalStripLLT.Components.DiagramProof.Complete.ChainStateSelection

/-! The single-chord path from `13` to `1n`, by opening and two actual flips. -/

namespace VerticalStripLLT.Circular.DiagramProof

set_option backward.isDefEq.respectTransparency false

private theorem opened_singleChord_selected {n : ℕ}
    (θ : Orientation (completeDiagram n)) (i j t : Fin (n + 1))
    (hi : i.val = 1) (hj : j.val = 2)
    (hθ : ∀ u v, (completeDiagram n).edgeData.selected θ.val u v ↔
      (u = 0 ∧ v = Fin.last n) ∨ (0 < u.val ∧ u.val + 1 = v.val) ∨
        (u = i ∧ v = t))
    (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (openCompleteChain θ j (by change 0 < j.val; lia)).val
      u v ↔ (u = 0 ∧ j ≤ v) ∨ (u = i ∧ (v = j ∨ v = t)) := by
  rw [openCompleteChain_selected, hθ]
  have hjn := Fin.le_last j
  have huv : u.val + 1 = v.val → 0 < u.val → ¬ j ≤ u → u = i ∧ v = j := by
    intro hstep hpos hlo
    apply And.intro <;> apply Fin.ext
    · change ¬ j.val ≤ u.val at hlo
      lia
    · change ¬ j.val ≤ u.val at hlo
      lia
  have hstep : i.val + 1 = j.val := by lia
  have hipos : 0 < i.val := by lia
  have hij : i < j := by change i.val < j.val; lia
  grind only

/-- The indicated two single-chord chain states connect without an induction hypothesis. -/
theorem complete_singleChord_path {n : ℕ}
    (θ η : Orientation (completeDiagram n)) (i j t : Fin (n + 1))
    (hi : i.val = 1) (hj : j.val = 2) (ht : t.val = 3) (htn : t ≤ Fin.last n)
    (hθ : ∀ u v, (completeDiagram n).edgeData.selected θ.val u v ↔
      (u = 0 ∧ v = Fin.last n) ∨ (0 < u.val ∧ u.val + 1 = v.val) ∨
        (u = i ∧ v = t))
    (hη : ∀ u v, (completeDiagram n).edgeData.selected η.val u v ↔
      (u = 0 ∧ v = Fin.last n) ∨ (0 < u.val ∧ u.val + 1 = v.val) ∨
        (u = i ∧ v = Fin.last n)) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  have hi0 : (0 : Fin (n + 1)) < i := by change 0 < i.val; lia
  have hij : i < j := by change i.val < j.val; lia
  have hjt : j < t := by change j.val < t.val; lia
  have hj0 := hi0.trans hij
  have hjn := hjt.trans_le htn
  have hin := hij.trans hjn
  have hit := hij.trans hjt
  have hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n := by
    intro v
    rw [hθ]
    simp [hi0.ne]
  have hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n := by
    intro v
    rw [hη]
    simp [hi0.ne]
  have hchainθ : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v := by
    intro u v hu huv
    exact (hθ u v).mpr (Or.inr (Or.inl ⟨hu, huv⟩))
  have hchainη : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v := by
    intro u v hu huv
    exact (hη u v).mpr (Or.inr (Or.inl ⟨hu, huv⟩))
  let α := openCompleteChain θ j hj0
  let β := openCompleteChain η j hj0
  have hα (u v) : (completeDiagram n).edgeData.selected α.val u v ↔
      (u = 0 ∧ j ≤ v) ∨ (u = i ∧ (v = j ∨ v = t)) :=
    opened_singleChord_selected θ i j t hi hj hθ u v
  have hβ (u v) : (completeDiagram n).edgeData.selected β.val u v ↔
      (u = 0 ∧ j ≤ v) ∨ (u = i ∧ (v = j ∨ v = Fin.last n)) :=
    opened_singleChord_selected η i j (Fin.last n) hi hj hη u v
  have hsink (w : Fin (n + 1)) (hw : j ≤ w) :
      ∀ x, ¬ (completeDiagram n).edgeData.selected α.val w x := by
    intro x hs
    rcases (hα w x).mp hs with ⟨hw0, _⟩ | ⟨hwi, _⟩
    · exact (not_le_of_gt hj0) (hw0 ▸ hw)
    · exact (not_le_of_gt hij) (hwi ▸ hw)
  have h13cover : Cover α i t := by
    apply relationCover_of_other_sinks
      (fun {_ _} h => α.selected_lt_of_forward (complete_forward n) h)
      ((hα i t).mpr (Or.inr ⟨rfl, Or.inr rfl⟩))
    intro w hw hwt
    rcases (hα i w).mp hw with ⟨hi0', _⟩ | ⟨_, hwj | hwt'⟩
    · exact (hi0.ne.symm hi0').elim
    · exact hsink w (hwj ▸ le_rfl)
    · exact (hwt hwt').elim
  have h03cover : Cover α 0 t := by
    apply relationCover_of_other_sinks
      (fun {_ _} h => α.selected_lt_of_forward (complete_forward n) h)
      ((hα 0 t).mpr (Or.inl ⟨rfl, hjt.le⟩))
    intro w hw _
    rcases (hα 0 w).mp hw with ⟨_, hwj⟩ | ⟨h0i, _⟩
    · exact hsink w hwj
    · exact (hi0.ne h0i).elim
  obtain ⟨γ, hαγ, _, h01cover, hγ⟩ :=
    exists_incomingSwap_of_covers (complete_forward n) α 0 i t h13cover h03cover hi0
  have hγroot : (completeDiagram n).edgeData.selected γ.val 0 (Fin.last n) := by
    rw [hγ]
    exact Or.inr ⟨(hα _ _).mpr (Or.inl ⟨rfl, hjn.le⟩), by simp [hi0.ne]⟩
  have hγcover : Cover γ 0 (Fin.last n) := by
    apply relationCover_of_last_incoming
      (fun {_ _} h => γ.selected_lt_of_forward (complete_forward n) h) hγroot
    intro z hz _ hs
    rw [hγ, hα] at hs
    have hz0 := hz.ne.symm
    have hnj := hjn.ne.symm
    grind only
  obtain ⟨δ, hγδ, _, _, hδ⟩ :=
    exists_outgoingSwap_of_covers (complete_forward n) γ 0 i (Fin.last n)
      h01cover hγcover hin
  have hδβ : δ = β := by
    apply fullSelection_injective
    ext e
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected, hδ, hγ, hα, hβ]
    have h0ine := hi0.ne
    have hjine := hij.ne.symm
    have hnj := hjn.ne.symm
    have htj := hjt.ne.symm
    have hji := not_le_of_gt hij
    grind only
  have hαβ : Relation.ReflTransGen (Flip (completeDiagram n)) α β :=
    hδβ ▸ ((Relation.ReflTransGen.single hαγ).tail hγδ)
  have hθα := reachable_openCompleteChain θ j hj0 hrowθ hchainθ
  have hηβ := reachable_openCompleteChain η j hj0 hrowη hchainη
  have reverse {σ τ : Orientation (completeDiagram n)}
      (h : Relation.ReflTransGen (Flip (completeDiagram n)) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram n)) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  exact hθα.trans (hαβ.trans (reverse hηβ))

/-- The same path in the finite chord-set representation. -/
theorem completeChainState_singleChord_reachable {n : ℕ} (hn : 3 ≤ n)
    (e f : Edge (completeDiagram n).area)
    (hetail : e.tail.val = 1) (hehead : e.head.val = 3)
    (hftail : f.tail.val = 1) (hfhead : f.head.val = n) :
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n {e}) (completeChainState n {f}) := by
  let j : Fin (n + 1) := ⟨2, by lia⟩
  have hfi : f.tail = e.tail := Fin.ext (hftail.trans hetail.symm)
  have hfn : f.head = Fin.last n := Fin.ext hfhead
  apply complete_singleChord_path _ _ e.tail j e.head hetail rfl hehead (Fin.le_last _)
  · intro u v
    rw [completeChainState_selected_singleton_iff (by lia)]
    exact or_congr Iff.rfl (or_congr Iff.rfl (and_congr eq_comm eq_comm))
  · intro u v
    rw [completeChainState_selected_singleton_iff (by lia), hfi, hfn]
    exact or_congr Iff.rfl (or_congr Iff.rfl (and_congr eq_comm eq_comm))

end VerticalStripLLT.Circular.DiagramProof

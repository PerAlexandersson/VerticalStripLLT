import VerticalStripLLT.Components.DiagramProof.Preparation.IncomingFlip

/-! Actual descending opening of an interval in a selected chain. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} [NeZero n] {D : Diagram n}

/-! The one-step form is stated with a natural threshold.  This avoids having
to represent the predecessor of the lower endpoint as a `Fin n`. -/
theorem exists_chain_opening_step_of_chain_above (hforward : Forward D) (θ ξ : Orientation D)
    (b t : Fin n) (hb : 0 < b) (q : ℕ) (hbq : b.val < q) (hqt : q ≤ t.val)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = t)
    (hchain : ∀ u v, b ≤ u → u.val + 1 = v.val → v ≤ t →
      D.edgeData.selected θ.val u v)
    (hrel : ∀ u v, D.edgeData.selected ξ.val u v ↔
      (u = 0 ∧ q ≤ v.val ∧ v.val ≤ t.val) ∨
        (D.edgeData.selected θ.val u v ∧
          ¬ (q ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) :
    ∃ η : Orientation D, Flip D ξ η ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = 0 ∧ q - 1 ≤ v.val ∧ v.val ≤ t.val) ∨
          (D.edgeData.selected θ.val u v ∧
            ¬ (q - 1 ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) := by
  let j : Fin n := ⟨q - 1, by
    have hbval : 0 < b.val := by exact hb
    have hqpos : 0 < q := lt_of_lt_of_le hbval hbq.le
    have hq_lt : q < n := lt_of_le_of_lt hqt t.isLt
    lia⟩
  let k : Fin n := ⟨q, by
    have hq_lt : q < n := lt_of_le_of_lt hqt t.isLt
    exact hq_lt⟩
  have hjpos : 0 < j := by
    change 0 < q - 1
    have hbpos : 0 < b.val := by exact hb
    lia
  have hjk : j < k := by
    change q - 1 < q
    lia
  have hkt : k ≤ t := by
    change q ≤ t.val
    exact hqt
  have hjkval : k.val = j.val + 1 := by
    change q = (q - 1) + 1
    exact (Nat.sub_add_cancel (by lia : 1 ≤ q)).symm
  have hseljkθ : D.edgeData.selected θ.val j k := by
    apply hchain j k (by
      change b.val ≤ q - 1
      lia) hjkval.symm hkt
  have hseljk : D.edgeData.selected ξ.val j k := by
    apply (hrel j k).mpr
    right
    refine ⟨hseljkθ, ?_⟩
    intro hh
    have hbad := hh.1
    change q ≤ q - 1 at hbad
    lia
  have hroot : D.edgeData.selected ξ.val 0 k := by
    apply (hrel 0 k).mpr
    left
    refine ⟨by simp, ?_, ?_⟩
    · exact le_rfl
    · exact hkt
  have hrootCover : Cover ξ 0 k := by
    apply relationCover_of_first_outgoing
      (fun {_ _} h => ξ.selected_lt_of_forward hforward h) hroot
    intro w hw0 hwk hsw
    rcases (hrel 0 w).mp hsw with ⟨_, hqv, hvt⟩ | ⟨hsθ, _⟩
    · change q ≤ w.val at hqv
      change w.val < q at hwk
      lia
    · rw [hrow w] at hsθ
      have hwt : w = t := hsθ
      subst w
      exact (not_lt_of_ge hkt) hwk
  have hjkCover : Cover ξ j k :=
    cover_of_selected_adjacent hseljk hjkval
  obtain ⟨η, hflip, _, _, hη⟩ :=
    exists_incomingSwap_of_covers hforward ξ 0 j k hjkCover hrootCover hjpos
  refine ⟨η, hflip, ?_⟩
  intro u v
  rw [hη, hrel]
  have hjval : j.val = q - 1 := rfl
  have hkval : k.val = q := rfl
  simp only [Fin.ext_iff, hjval, hkval]
  grind

theorem exists_chain_opening_step (hforward : Forward D) (θ ξ : Orientation D)
    (b t : Fin n) (hb : 0 < b) (q : ℕ) (hbq : b.val < q) (hqt : q ≤ t.val)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = t)
    (hchain : ∀ u v, 0 < u → u.val + 1 = v.val → v ≤ t →
      D.edgeData.selected θ.val u v)
    (hrel : ∀ u v, D.edgeData.selected ξ.val u v ↔
      (u = 0 ∧ q ≤ v.val ∧ v.val ≤ t.val) ∨
        (D.edgeData.selected θ.val u v ∧
          ¬ (q ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) :
    ∃ η : Orientation D, Flip D ξ η ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = 0 ∧ q - 1 ≤ v.val ∧ v.val ≤ t.val) ∨
          (D.edgeData.selected θ.val u v ∧
            ¬ (q - 1 ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) := by
  exact exists_chain_opening_step_of_chain_above hforward θ ξ b t hb q hbq hqt hrow
    (fun u v hbu huv hvt => hchain u v (hb.trans_le hbu) huv hvt) hrel

/-! Open the chain by the actual incoming swaps
`(t-1)t, (t-2)(t-1), ..., b(b+1)`. -/
theorem exists_chain_opening_of_chain_above (hforward : Forward D) (θ : Orientation D)
    (b t : Fin n) (hb : 0 < b) (hbt : b ≤ t)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = t)
    (hchain : ∀ u v, b ≤ u → u.val + 1 = v.val → v ≤ t →
      D.edgeData.selected θ.val u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = 0 ∧ b ≤ v ∧ v ≤ t) ∨
          (D.edgeData.selected θ.val u v ∧
            ¬ (b ≤ u ∧ u.val + 1 = v.val ∧ v ≤ t))) := by
  have aux : ∀ q : ℕ, b.val ≤ q → q ≤ t.val →
      ∀ ξ : Orientation D, (∀ u v, D.edgeData.selected ξ.val u v ↔
        (u = 0 ∧ q ≤ v.val ∧ v.val ≤ t.val) ∨
          (D.edgeData.selected θ.val u v ∧
            ¬ (q ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) →
      ∃ η : Orientation D, Relation.ReflTransGen (Flip D) ξ η ∧
        (∀ u v, D.edgeData.selected η.val u v ↔
          (u = 0 ∧ b.val ≤ v.val ∧ v.val ≤ t.val) ∨
            (D.edgeData.selected θ.val u v ∧
              ¬ (b.val ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val))) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hbq hqt ξ hξ
        by_cases hqb : q = b.val
        · subst q
          refine ⟨ξ, Relation.ReflTransGen.refl, ?_⟩
          intro u v
          exact hξ u v
        · have hbq' : b.val < q := lt_of_le_of_ne hbq (Ne.symm hqb)
          obtain ⟨ζ, hξζ, hζ⟩ :=
            exists_chain_opening_step_of_chain_above hforward θ ξ b t hb q
            hbq' hqt hrow hchain hξ
          have hqpred : b.val ≤ q - 1 := by lia
          have hpredlt : q - 1 < q := by lia
          obtain ⟨η, hζη, hη⟩ :=
            ih (q - 1) hpredlt hqpred ((Nat.sub_le q 1).trans hqt) ζ hζ
          refine ⟨η, (Relation.ReflTransGen.single hξζ).trans hζη, ?_⟩
          exact hη
  have hstart : ∀ u v, D.edgeData.selected θ.val u v ↔
      (u = 0 ∧ t.val ≤ v.val ∧ v.val ≤ t.val) ∨
        (D.edgeData.selected θ.val u v ∧
          ¬ (t.val ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ t.val)) := by
    intro u v
    constructor
    · intro h
      by_cases hu : u = 0
      · subst u
        left
        refine ⟨rfl, ?_, ?_⟩
        · rw [hrow v] at h
          exact (congrArg Fin.val h).ge
        · rw [hrow v] at h
          exact (congrArg Fin.val h).le
      · right
        refine ⟨h, ?_⟩
        intro hh
        have huv := θ.selected_lt_of_forward hforward h
        have hvt : v.val ≤ t.val := hh.2.2
        have hut : t.val ≤ u.val := hh.1
        lia
    · rintro (⟨hu, hvt, _⟩ | ⟨h, _⟩)
      · subst u
        rw [hrow v]
        apply Fin.ext
        lia
      · exact h
  have hbtval : b.val ≤ t.val := Fin.le_iff_val_le_val.mp hbt
  obtain ⟨η, hpath, hη⟩ := aux t.val hbtval le_rfl θ hstart
  refine ⟨η, hpath, ?_⟩
  intro u v
  simpa only [Fin.le_iff_val_le_val] using hη u v

theorem exists_chain_opening (hforward : Forward D) (θ : Orientation D)
    (b t : Fin n) (hb : 0 < b) (hbt : b ≤ t)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = t)
    (hchain : ∀ u v, 0 < u → u.val + 1 = v.val → v ≤ t →
      D.edgeData.selected θ.val u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = 0 ∧ b ≤ v ∧ v ≤ t) ∨
          (D.edgeData.selected θ.val u v ∧
            ¬ (b ≤ u ∧ u.val + 1 = v.val ∧ v ≤ t))) := by
  exact exists_chain_opening_of_chain_above hforward θ b t hb hbt hrow
    (fun u v hbu huv hvt => hchain u v (hb.trans_le hbu) huv hvt)

end

end VerticalStripLLT.Circular.DiagramProof

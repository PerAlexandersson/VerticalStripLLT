import VerticalStripLLT.Components.DiagramProof.Corrections.CornerCorrections

/-!
# Reordering selected weak blocks

Every selected edge and every actual flip stays inside a selected weak block.
We place the blocks consecutively: the block of the greatest vertex last, the
others by their least vertices, each block internally increasing. Keeping the
natural edges inside blocks gives an ordinary diagram on the same vertex set,
and the reordering carries the whole component bijectively onto a whole
component. It fixes the greatest vertex, so both right-marked values are
preserved. If the natural graph is connected and the selected relation is not,
some natural edge joins two blocks and is discarded, so the natural area drops.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D) (θ : Orientation D)

/-! ### The sorting key -/

/-- The least vertex of the weak block of `v`. -/
def blockMin (v : Fin (k + 1)) : Fin (k + 1) :=
  (Finset.univ.filter fun w => WeakReach θ v w).min'
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.EqvGen.refl v⟩⟩

/-- Whether `v` lies in the block of the greatest vertex. -/
def blockFlag (v : Fin (k + 1)) : ℕ := if WeakReach θ v (Fin.last k) then 1 else 0

/-- Sort by block flag, then least block vertex, then the vertex itself. -/
def blockKey (v : Fin (k + 1)) : ℕ :=
  (blockFlag θ v * (k + 1) + (blockMin θ v).val) * (k + 1) + v.val

theorem blockMin_reach (v : Fin (k + 1)) : WeakReach θ v (blockMin θ v) := by
  have h := Finset.min'_mem (Finset.univ.filter fun w => WeakReach θ v w)
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.EqvGen.refl v⟩⟩
  exact (Finset.mem_filter.mp h).2

theorem blockMin_le (v w : Fin (k + 1)) (h : WeakReach θ v w) : blockMin θ v ≤ w :=
  Finset.min'_le _ _ (by simpa using h)

theorem blockMin_eq {u v : Fin (k + 1)} (h : WeakReach θ u v) : blockMin θ u = blockMin θ v := by
  apply le_antisymm
  · exact blockMin_le θ u _ (Relation.EqvGen.trans _ _ _ h (blockMin_reach θ v))
  · exact blockMin_le θ v _ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h)
      (blockMin_reach θ u))

theorem blockFlag_eq {u v : Fin (k + 1)} (h : WeakReach θ u v) :
    blockFlag θ u = blockFlag θ v := by
  unfold blockFlag
  have : WeakReach θ u (Fin.last k) ↔ WeakReach θ v (Fin.last k) :=
    ⟨fun h' => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) h',
      fun h' => Relation.EqvGen.trans _ _ _ h h'⟩
  simp only [this]

theorem blockFlag_le (v : Fin (k + 1)) : blockFlag θ v ≤ 1 := by
  unfold blockFlag
  split_ifs <;> simp

theorem blockKey_lt_iff_of_reach {u v : Fin (k + 1)} (h : WeakReach θ u v) :
    blockKey θ u < blockKey θ v ↔ u < v := by
  unfold blockKey
  rw [blockMin_eq θ h, blockFlag_eq θ h, Fin.lt_def]
  exact Nat.add_lt_add_iff_left

theorem blockKey_injective : Function.Injective (blockKey θ) := by
  intro u v h
  apply Fin.ext
  have h1 := congrArg (· % (k + 1)) h
  simp only [blockKey, Nat.add_comm _ (Fin.val _), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt v.isLt] at h1
  exact h1

/-- The key of a vertex determines its block prefix. -/
theorem blockKey_div (v : Fin (k + 1)) :
    blockKey θ v / (k + 1) = blockFlag θ v * (k + 1) + (blockMin θ v).val := by
  unfold blockKey
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos k), Nat.div_eq_of_lt v.isLt,
    zero_add]

/-- Vertices with keys between two vertices of one block lie in that block. -/
theorem reach_of_blockKey_between {u v w : Fin (k + 1)} (huv : WeakReach θ u v)
    (huw : blockKey θ u ≤ blockKey θ w) (hwv : blockKey θ w ≤ blockKey θ v) :
    WeakReach θ u w := by
  have heq : blockKey θ u / (k + 1) = blockKey θ v / (k + 1) := by
    rw [blockKey_div, blockKey_div, blockMin_eq θ huv, blockFlag_eq θ huv]
  have h1 : blockKey θ u / (k + 1) ≤ blockKey θ w / (k + 1) := Nat.div_le_div_right huw
  have h2 : blockKey θ w / (k + 1) ≤ blockKey θ v / (k + 1) := Nat.div_le_div_right hwv
  have hP : blockKey θ w / (k + 1) = blockKey θ u / (k + 1) :=
    le_antisymm (h2.trans heq.symm.le) h1
  rw [blockKey_div, blockKey_div] at hP
  have hmod := congrArg (· % (k + 1)) hP
  simp only [Nat.add_comm (blockFlag θ _ * (k + 1)), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (blockMin θ _).isLt] at hmod
  have hmin : blockMin θ w = blockMin θ u := Fin.ext hmod
  have h3 : WeakReach θ (blockMin θ u) w := by
    rw [← hmin]
    exact Relation.EqvGen.symm _ _ (blockMin_reach θ w)
  exact Relation.EqvGen.trans _ _ _ (blockMin_reach θ u) h3

theorem blockKey_le_last (w : Fin (k + 1)) : blockKey θ w ≤ blockKey θ (Fin.last k) := by
  have hlast : blockFlag θ (Fin.last k) = 1 := by
    unfold blockFlag
    exact ite_eq_left (show WeakReach θ (Fin.last k) (Fin.last k) from Relation.EqvGen.refl _)
  by_cases hw : WeakReach θ w (Fin.last k)
  · rcases eq_or_ne w (Fin.last k) with rfl | hne
    · exact le_rfl
    · exact ((blockKey_lt_iff_of_reach θ hw).mpr (lt_of_le_of_ne (Fin.le_last w) hne)).le
  · have hw0 : blockFlag θ w = 0 := by simp [blockFlag, hw]
    unfold blockKey
    rw [hw0, hlast]
    have hm := (blockMin θ w).isLt
    have hv := w.isLt
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by lia)) (by simp; lia)

/-! ### The rank permutation -/

/-- The rank of a vertex in the key order. -/
def blockRank (v : Fin (k + 1)) : Fin (k + 1) :=
  ⟨(Finset.univ.filter fun w => blockKey θ w < blockKey θ v).card, by
    refine (Finset.card_lt_card (Finset.filter_ssubset.mpr
      ⟨v, Finset.mem_univ _, lt_irrefl (blockKey θ v)⟩)).trans_eq ?_
    simp⟩

theorem blockRank_lt_iff (u v : Fin (k + 1)) :
    blockRank θ u < blockRank θ v ↔ blockKey θ u < blockKey θ v := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    apply (not_lt_of_ge _) h
    change (Finset.univ.filter fun w => blockKey θ w < blockKey θ v).card ≤
      (Finset.univ.filter fun w => blockKey θ w < blockKey θ u).card
    exact Finset.card_le_card (fun w hw => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact lt_of_lt_of_le hw hle)
  · intro h
    change (Finset.univ.filter fun w => blockKey θ w < blockKey θ u).card <
      (Finset.univ.filter fun w => blockKey θ w < blockKey θ v).card
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨u, by simpa using h, by simp⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.trans h

theorem blockRank_injective : Function.Injective (blockRank θ) := by
  intro u v h
  apply blockKey_injective θ
  rcases lt_trichotomy (blockKey θ u) (blockKey θ v) with h' | h' | h'
  · exact absurd h (ne_of_lt ((blockRank_lt_iff θ u v).mpr h'))
  · exact h'
  · exact absurd h (ne_of_gt ((blockRank_lt_iff θ v u).mpr h'))

/-- The blockwise reordering permutation. -/
def blockPerm : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (blockRank θ) (Finite.injective_iff_bijective.mp (blockRank_injective θ))

theorem blockPerm_apply (v : Fin (k + 1)) : blockPerm θ v = blockRank θ v := rfl

theorem blockPerm_lt_iff (u v : Fin (k + 1)) :
    blockPerm θ u < blockPerm θ v ↔ blockKey θ u < blockKey θ v :=
  blockRank_lt_iff θ u v

theorem blockPerm_lt_iff_of_reach {u v : Fin (k + 1)} (h : WeakReach θ u v) :
    blockPerm θ u < blockPerm θ v ↔ u < v :=
  (blockPerm_lt_iff θ u v).trans (blockKey_lt_iff_of_reach θ h)

theorem blockPerm_last : blockPerm θ (Fin.last k) = Fin.last k := by
  apply le_antisymm (Fin.le_last _)
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw⟩ := (blockPerm θ).surjective (Fin.last k)
  have := (blockPerm_lt_iff θ (Fin.last k) w).mp (lt_of_lt_of_eq hlt hw.symm)
  exact absurd (blockKey_le_last θ w) (not_le_of_gt this)

theorem blockPerm_le_iff_of_reach {u v : Fin (k + 1)} (h : WeakReach θ u v) :
    blockPerm θ u ≤ blockPerm θ v ↔ u ≤ v := by
  rw [← not_lt, ← not_lt, blockPerm_lt_iff_of_reach θ (Relation.EqvGen.symm _ _ h)]

/-- The image of a block is an interval. -/
theorem reach_of_blockPerm_between {u v : Fin (k + 1)} (huv : WeakReach θ u v)
    {w' : Fin (k + 1)} (h1 : blockPerm θ u ≤ w') (h2 : w' ≤ blockPerm θ v) :
    ∃ w, blockPerm θ w = w' ∧ WeakReach θ u w := by
  obtain ⟨w, rfl⟩ := (blockPerm θ).surjective w'
  refine ⟨w, rfl, reach_of_blockKey_between θ huv ?_ ?_⟩
  · by_contra h
    push Not at h
    exact absurd h1 (not_le_of_gt ((blockPerm_lt_iff θ w u).mpr h))
  · by_contra h
    push Not at h
    exact absurd h2 (not_le_of_gt ((blockPerm_lt_iff θ v w).mpr h))

/-! ### The reordered diagram -/

/-- Natural pairs inside one block, relabelled. -/
def blockNatural (u' v' : Fin (k + 1)) : Prop :=
  naturalRel D ((blockPerm θ).symm u') ((blockPerm θ).symm v') ∧
    WeakReach θ ((blockPerm θ).symm u') ((blockPerm θ).symm v')

/-- Strict pairs, relabelled; they are always inside a block. -/
def blockStrict (u' v' : Fin (k + 1)) : Prop :=
  strictRel D ((blockPerm θ).symm u') ((blockPerm θ).symm v')

include hD in
theorem blockNatural_ordinary : OrdinaryRelation (blockNatural θ) := by
  refine ⟨?_, ?_⟩
  · rintro u' v' ⟨hn, hr⟩
    obtain ⟨u, rfl⟩ := (blockPerm θ).surjective u'
    obtain ⟨v, rfl⟩ := (blockPerm θ).surjective v'
    simp only [Equiv.symm_apply_apply] at hn hr
    exact (blockPerm_lt_iff_of_reach θ hr).mpr (naturalRel_forward hD hn)
  · rintro u' w' v' ⟨hn, hr⟩ huw hwv
    obtain ⟨u, rfl⟩ := (blockPerm θ).surjective u'
    obtain ⟨v, rfl⟩ := (blockPerm θ).surjective v'
    simp only [Equiv.symm_apply_apply] at hn hr
    obtain ⟨w, rfl, huwr⟩ := reach_of_blockPerm_between θ hr huw.le hwv.le
    have hwv' : WeakReach θ w v :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ huwr) hr
    have huw' := (blockPerm_lt_iff_of_reach θ huwr).mp huw
    have hwv'' := (blockPerm_lt_iff_of_reach θ hwv').mp hwv
    obtain ⟨h1, h2⟩ := naturalRel_interval hD hn huw' hwv''
    simp only [blockNatural, Equiv.symm_apply_apply]
    exact ⟨⟨h1, huwr⟩, ⟨h2, hwv'⟩⟩

theorem weakReach_of_selected {u v : Fin (k + 1)} (h : D.edgeData.selected θ.val u v) :
    WeakReach θ u v := Relation.EqvGen.rel _ _ h

include hD in
theorem blockStrict_maximal (s' t' : Fin (k + 1)) (h : blockStrict θ s' t') :
    MaximalPair (blockNatural θ) s' t' := by
  obtain ⟨s, rfl⟩ := (blockPerm θ).surjective s'
  obtain ⟨t, rfl⟩ := (blockPerm θ).surjective t'
  unfold blockStrict at h
  simp only [Equiv.symm_apply_apply] at h
  have hst : WeakReach θ s t := weakReach_of_selected θ (selected_of_strictRel θ h)
  refine ⟨by simpa [blockNatural] using ⟨naturalRel_of_strictRel h, hst⟩, ?_⟩
  intro x' y' hxy hxs hty
  obtain ⟨x, rfl⟩ := (blockPerm θ).surjective x'
  obtain ⟨y, rfl⟩ := (blockPerm θ).surjective y'
  obtain ⟨hn, hr⟩ := hxy
  simp only [Equiv.symm_apply_apply] at hn hr
  have hlt : blockPerm θ s < blockPerm θ t := (blockPerm_lt_iff_of_reach θ hst).mpr
    (naturalRel_forward hD (naturalRel_of_strictRel h))
  obtain ⟨s₁, hs₁, hxs₁⟩ := reach_of_blockPerm_between θ hr hxs (hlt.le.trans hty)
  obtain ⟨t₁, ht₁, hxt₁⟩ := reach_of_blockPerm_between θ hr (hxs.trans hlt.le) hty
  rw [(blockPerm θ).injective hs₁] at hxs₁
  rw [(blockPerm θ).injective ht₁] at hxt₁
  have hxs' := (blockPerm_le_iff_of_reach θ hxs₁).mp hxs
  have hyt : WeakReach θ t y := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ hxt₁) hr
  have hty' := (blockPerm_le_iff_of_reach θ hyt).mp hty
  obtain ⟨h1, h2⟩ := strictRel_maximal hD h hn hxs' hty'
  exact ⟨congrArg _ h1, congrArg _ h2⟩

/-- The diagram with the selected blocks placed consecutively. -/
def blockDiagram : Diagram (k + 1) :=
  ofRelations (blockNatural θ) (blockStrict θ) (blockNatural_ordinary hD θ)
    (blockStrict_maximal hD θ) D.area.positive

theorem blockDiagram_forward : Forward (blockDiagram hD θ) := ofRelations_forward _ _ _ _ _

theorem blockDiagram_naturalRel (u v : Fin (k + 1)) :
    naturalRel (blockDiagram hD θ) u v ↔ blockNatural θ u v := ofRelations_naturalRel ..

theorem blockDiagram_strictRel (u v : Fin (k + 1)) :
    strictRel (blockDiagram hD θ) u v ↔ blockStrict θ u v := ofRelations_strictRel ..

/-- The reordered state corresponds to `θ`. -/
theorem exists_blockState :
    ∃ θ' : Orientation (blockDiagram hD θ), Corresponds (blockPerm θ) θ θ' := by
  obtain ⟨θ', hθ'⟩ := exists_orientation_of_relation (blockDiagram_forward hD θ)
    (fun u' v' => D.edgeData.selected θ.val ((blockPerm θ).symm u') ((blockPerm θ).symm v'))
    (fun u' v' h => (blockDiagram_naturalRel hD θ u' v').mpr
      ⟨naturalRel_of_selected h, weakReach_of_selected θ h⟩)
    (fun u' v' h => selected_of_strictRel θ ((blockDiagram_strictRel hD θ u' v').mp h))
  refine ⟨θ', fun u v => ?_, fun u v huv => (blockPerm_lt_iff_of_reach θ huv).symm⟩
  rw [hθ', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Disconnected selection in a connected natural graph discards a natural pair. -/
theorem blockDiagram_measureLT
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v) (hdis : ¬ SelectedConnected θ) :
    MeasureLT (blockDiagram hD θ) D := by
  left
  -- Some natural pair joins two blocks.
  have hcross : ∃ x y, naturalRel D x y ∧ ¬ WeakReach θ x y := by
    by_contra hno
    push Not at hno
    apply hdis
    intro u v
    have key : ∀ a b, Relation.EqvGen (naturalRel D) a b → WeakReach θ a b := by
      intro a b hab
      induction hab with
      | rel a b h => exact hno a b h
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    exact key u v (hconn u v)
  obtain ⟨x, y, hxy, hnr⟩ := hcross
  let f : Fin (k + 1) × Fin (k + 1) ↪ Fin (k + 1) × Fin (k + 1) :=
    ⟨fun p => ((blockPerm θ).symm p.1, (blockPerm θ).symm p.2), by
      intro p q h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext ((blockPerm θ).symm.injective h1) ((blockPerm θ).symm.injective h2)⟩
  rw [naturalArea_eq_card, naturalArea_eq_card, ← Finset.card_map f]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(x, y), mem_naturalPairs.mpr hxy, ?_⟩
    intro hmem
    obtain ⟨p, hp, hpe⟩ := Finset.mem_map.mp hmem
    have := (blockDiagram_naturalRel hD θ p.1 p.2).mp (mem_naturalPairs.mp hp)
    obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
    exact hnr (by simpa only [← h1, ← h2] using this.2)
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    exact mem_naturalPairs.mpr ((blockDiagram_naturalRel hD θ p.1 p.2).mp
      (mem_naturalPairs.mp hp)).1

/-- **Block reordering.** A disconnected component of a naturally connected
diagram is a whole component of a smaller diagram, with the same marked values. -/
theorem certifies_disconnected
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v) (hdis : ¬ SelectedConnected θ) :
    ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  obtain ⟨θ', hc⟩ := exists_blockState hD θ
  have hB := blockDiagram_forward hD θ
  refine ⟨Finsupp.single ⟨blockDiagram hD θ, hB, θ'⟩ 1, fun m β => ?_,
    Cert.smaller_single (blockDiagram_measureLT hD θ hconn hdis)⟩
  simp only [Cert.K_single, Cert.E_single, one_smul]
  exact ⟨(hc.componentMarkedK_eq hD hB (blockPerm_last θ) m β).symm,
    (hc.componentMarkedE_eq hD hB (blockPerm_last θ) m β).symm⟩

end

end VerticalStripLLT.Circular.DiagramProof

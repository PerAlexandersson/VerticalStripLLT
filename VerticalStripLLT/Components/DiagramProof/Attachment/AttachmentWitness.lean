import VerticalStripLLT.Components.DiagramProof.Attachment.RightAttachment
import VerticalStripLLT.Components.DiagramProof.Attachment.FirstDrop

/-!
# Witnesses and saturation on the left side of an attachment

A natural pair of the union containing a pair of the left side lies on the left
side. Hence maximal corners of the left side are maximal in the union, a saturated
union has a saturated left side, and the left restriction of a connected
common-cover state is again a connected common-cover state.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

namespace IsRightAttachment

variable {p q : ℕ} {G : Diagram (p + q + 1)} {L : Diagram (p + 1)} {R : Diagram (q + 1)}
  (h : IsRightAttachment G L R)

include h

theorem maximalPair_left {s t : Fin (p + 1)} (hst : MaximalPair (naturalRel L) s t) :
    MaximalPair (naturalRel G) (attachLeft p q s) (attachLeft p q t) := by
  refine ⟨(h.natural_left s t).mpr hst.1, ?_⟩
  intro a b hab has htb
  rcases (h.natural a b).mp hab with ⟨a', b', rfl, rfl, hab'⟩ | ⟨a', b', rfl, rfl, hab'⟩
  · obtain ⟨h1, h2⟩ := hst.2 a' b' hab' ((attachLeft p q).le_iff_le.mp has)
      ((attachLeft p q).le_iff_le.mp htb)
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  · exfalso
    have hst' := naturalRel_forward h.forwardL hst.1
    have h1 : (attachRight p q a').val ≤ (attachLeft p q s).val := has
    have h2 : (attachLeft p q t).val ≤ p := by
      have := t.isLt
      simp only [attachLeft_val]
      lia
    have h3 : s.val < t.val := hst'
    simp only [attachLeft_val, attachRight_val] at h1 h2
    lia

theorem saturated_left (hsat : ∀ s t, MaximalPair (naturalRel G) s t → strictRel G s t)
    (s t : Fin (p + 1)) (hst : MaximalPair (naturalRel L) s t) : strictRel L s t :=
  (h.strict_left s t).mp (hsat _ _ (h.maximalPair_left hst))

/-- The left restriction of a connected state is connected. -/
theorem connected_restrictLeft {θ : Orientation G} (hθ : SelectedConnected θ) :
    SelectedConnected (h.restrictLeft θ) := by
  let proj : Fin (p + q + 1) → Fin (p + 1) := fun u =>
    if hu : u.val ≤ p then ⟨u.val, by lia⟩ else Fin.last p
  have hprojL (a : Fin (p + 1)) : proj (attachLeft p q a) = a := by
    have := a.isLt
    simp only [proj, attachLeft_val]
    rw [dite_eq_left (by lia)]
  have hprojR (a : Fin (q + 1)) : proj (attachRight p q a) = Fin.last p := by
    simp only [proj, attachRight_val]
    by_cases ha : p + a.val ≤ p
    · rw [dite_eq_left ha]
      exact Fin.ext (by simp; lia)
    · rw [dite_eq_right ha]
  have hstep : ∀ u v, G.edgeData.selected θ.val u v →
      WeakReach (h.restrictLeft θ) (proj u) (proj v) := by
    intro u v huv
    rcases (h.selected_iff θ u v).mp huv with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, -⟩
    · rw [hprojL, hprojL]
      exact Relation.EqvGen.rel _ _ hab
    · rw [hprojR, hprojR]
      exact Relation.EqvGen.refl _
  intro x y
  have key : ∀ u v, WeakReach θ u v → WeakReach (h.restrictLeft θ) (proj u) (proj v) := by
    intro u v huv
    induction huv with
    | rel u v hs => exact hstep u v hs
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  simpa only [hprojL] using key _ _ (hθ (attachLeft p q x) (attachLeft p q y))

/-- The left restriction of a common-cover state is a common-cover state. -/
theorem commonCover_restrictLeft {θ : Orientation G} (hθ : (allCorners G).CommonCover θ) :
    (allCorners L).CommonCover (h.restrictLeft θ) := by
  intro e he
  have heC := (isCorner_iff_maximalPair h.forwardL e).mp (Finset.mem_filter.mp he).2
  have hG := h.maximalPair_left heC
  obtain ⟨f, hft, hfh⟩ := hG.1
  have hfC : IsCorner f := by
    rw [isCorner_iff_maximalPair h.forward, hft, hfh]
    exact hG
  have hcov := hθ f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfC⟩)
  rw [hft, hfh, ← h.glue_restrict θ] at hcov
  exact (h.cover_left _ _ _ _).mp hcov

/-- The left restriction of a component with a witness has a witness. -/
theorem hasCommonWitness_restrictLeft {θ : Orientation G} (hθ : HasCommonWitness θ) :
    HasCommonWitness (h.restrictLeft θ) := by
  obtain ⟨η, hη, hcη, hccη⟩ := hθ
  exact ⟨h.restrictLeft η, mem_flipComponent_iff.mpr
    (h.reachable_restrict (mem_flipComponent_iff.mp hη)).1,
    h.connected_restrictLeft hcη, h.commonCover_restrictLeft hccη⟩

end IsRightAttachment

end

end VerticalStripLLT.Circular.DiagramProof

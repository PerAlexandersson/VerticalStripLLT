import VerticalStripLLT.Components.DiagramProof.ReversedRelations
import VerticalStripLLT.Components.DiagramProof.GoodEdges
import VerticalStripLLT.Components.DiagramProof.WeakBlocks

/-! Reversing selected diagrams, cover tests, and actual flip paths. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D E : Diagram n}

/-- Transport the full selected edge set through a reversal of the natural edges. -/
def reverseOrientation (hE : Forward E) (ρ : Edge D.area ≃ Edge E.area)
    (hstrict : ∀ e, ρ e ∈ E.strict ↔ e ∈ D.strict) (θ : Orientation D) :
    Orientation E :=
  ofFullSelection hE ((fullSelection θ).map ρ.toEmbedding) (by
    intro e he
    refine Finset.mem_map.mpr ⟨ρ.symm e, Finset.mem_union_left _ ?_, by simp⟩
    exact (hstrict (ρ.symm e)).mp (by simpa using he))

@[simp]
theorem fullSelection_reverseOrientation (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict) (θ : Orientation D) :
    fullSelection (reverseOrientation hE ρ hstrict θ) =
      (fullSelection θ).map ρ.toEmbedding :=
  fullSelection_ofFullSelection _ _ _

@[simp]
theorem totalSelected_reverseOrientation (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict) (θ : Orientation D) :
    totalSelected (reverseOrientation hE ρ hstrict θ) = totalSelected θ := by
  simp [totalSelected]

theorem reverseOrientation_mem (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict) (θ : Orientation D) (e : Edge D.area) :
    ρ e ∈ (reverseOrientation hE ρ hstrict θ).val ↔ e ∈ θ.val := by
  rw [← fullSelection_sdiff_strict, Finset.mem_sdiff,
    fullSelection_reverseOrientation]
  simp only [Finset.mem_map_equiv, hstrict, ← Finset.mem_sdiff,
    Equiv.symm_apply_apply, fullSelection_sdiff_strict]

theorem reverseOrientation_selected (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev) (θ : Orientation D) (u v : Fin n) :
    E.edgeData.selected (reverseOrientation hE ρ hstrict θ).val u v ↔
      D.edgeData.selected θ.val v.rev u.rev := by
  constructor
  · rintro ⟨e, he, ht, hh⟩
    change e ∈ fullSelection (reverseOrientation hE ρ hstrict θ) at he
    rw [fullSelection_reverseOrientation] at he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    change (ρ f).tail = u at ht
    change (ρ f).head = v at hh
    refine ⟨f, hf, ?_, ?_⟩
    · change f.tail = v.rev
      simpa only [hhead, Fin.rev_rev] using congrArg Fin.rev hh
    · change f.head = u.rev
      simpa only [htail, Fin.rev_rev] using congrArg Fin.rev ht
  · rintro ⟨e, he, ht, hh⟩
    refine ⟨ρ e, ?_, ?_, ?_⟩
    · change ρ e ∈ fullSelection (reverseOrientation hE ρ hstrict θ)
      rw [fullSelection_reverseOrientation]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    · change (ρ e).tail = u
      change e.head = u.rev at hh
      simp only [htail, hh, Fin.rev_rev]
    · change (ρ e).head = v
      change e.tail = v.rev at ht
      simp only [hhead, ht, Fin.rev_rev]

theorem reverseOrientation_cover (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev) (θ : Orientation D) (u v : Fin n) :
    Cover (reverseOrientation hE ρ hstrict θ) u v ↔ Cover θ v.rev u.rev :=
  relationCover_rev_iff (reverseOrientation_selected hE ρ hstrict htail hhead θ) u v

theorem reverseOrientation_weakReach (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev) (θ : Orientation D) (u v : Fin n) :
    WeakReach (reverseOrientation hE ρ hstrict θ) u v ↔ WeakReach θ u.rev v.rev :=
  eqvGen_rev_iff (reverseOrientation_selected hE ρ hstrict htail hhead θ) u v

theorem reverseOrientation_connected (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev) (θ : Orientation D) :
    SelectedConnected (reverseOrientation hE ρ hstrict θ) ↔ SelectedConnected θ := by
  constructor
  · intro h u v
    simpa only [Fin.rev_rev] using
      (reverseOrientation_weakReach hE ρ hstrict htail hhead θ u.rev v.rev).mp
        (h u.rev v.rev)
  · intro h u v
    exact (reverseOrientation_weakReach hE ρ hstrict htail hhead θ u v).mpr
      (h u.rev v.rev)

theorem reverseOrientation_commonCover (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev)
    (hcorner : ∀ e, IsCorner (ρ e) ↔ IsCorner e) (θ : Orientation D) :
    (allCorners E).CommonCover (reverseOrientation hE ρ hstrict θ) ↔
      (allCorners D).CommonCover θ := by
  have hcover (e : Edge D.area) :
      Cover (reverseOrientation hE ρ hstrict θ) (ρ e).tail (ρ e).head ↔
        Cover θ e.tail e.head := by
    rw [htail, hhead, reverseOrientation_cover hE ρ hstrict htail hhead]
    simp only [Fin.rev_rev]
  constructor
  · intro h e he
    apply (hcover e).mp
    apply h (ρ e)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcorner e).mpr (Finset.mem_filter.mp he).2⟩
  · intro h f hf
    obtain ⟨e, rfl⟩ := ρ.surjective f
    apply (hcover e).mpr
    apply h e
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcorner e).mp (Finset.mem_filter.mp hf).2⟩

theorem reverseOrientation_inverse (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (hstrict' : ∀ e, ρ.symm e ∈ D.strict ↔ e ∈ E.strict) (θ : Orientation D) :
    reverseOrientation hD ρ.symm hstrict' (reverseOrientation hE ρ hstrict θ) = θ := by
  apply fullSelection_injective
  ext e
  simp only [fullSelection_reverseOrientation, Finset.mem_map_equiv,
    Equiv.symm_symm, Equiv.symm_apply_apply]

/-- Reflection gives a bijection of the actual orientations, retaining all strict markings. -/
def reverseOrientationEquiv (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area)
    (hstrict : ∀ e, ρ e ∈ E.strict ↔ e ∈ D.strict) : Orientation D ≃ Orientation E where
  toFun := reverseOrientation hE ρ hstrict
  invFun := reverseOrientation hD ρ.symm (fun e => by
    simpa only [Equiv.apply_symm_apply] using (hstrict (ρ.symm e)).symm)
  left_inv := reverseOrientation_inverse hD hE ρ hstrict _
  right_inv := reverseOrientation_inverse hE hD ρ.symm _ hstrict

/-- Reflecting the triangle reverses the direction of a directed flip. -/
def reverseDirectedFlip (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev)
    {θ η : Orientation D} (w : DirectedFlipWitness D θ η) :
    DirectedFlipWitness E (reverseOrientation hE ρ hstrict η)
      (reverseOrientation hE ρ hstrict θ) := by
  let a := w.eab.tail
  let b := w.eab.head
  let c := w.ebc.head
  let wn := w.normalizeForward hD
  have sab : Cover θ a b := (liftCover_iff_cover hD θ a b).mp wn.source_ab
  have sac : Cover θ a c := (liftCover_iff_cover hD θ a c).mp wn.source_ac
  have tac : Cover η a c := (liftCover_iff_cover hD η a c).mp wn.target_ac
  have tbc : Cover η b c := (liftCover_iff_cover hD η b c).mp wn.target_bc
  have snbc : ¬ Cover θ b c := fun h =>
    wn.source_not_bc ((liftCover_iff_cover hD θ b c).mpr h)
  have tnab : ¬ Cover η a b := fun h =>
    wn.target_not_ab ((liftCover_iff_cover hD η a b).mpr h)
  have hcovers (σ : Orientation D) (u v : Fin n) :
      Cover (reverseOrientation hE ρ hstrict σ) v.rev u.rev ↔ Cover σ u v := by
    simpa only [Fin.rev_rev] using
      reverseOrientation_cover hE ρ hstrict htail hhead σ v.rev u.rev
  have hnormal (e : Edge D.area) (he : e ∈ D.edgeData.normalEdges) :
      ρ e ∈ E.edgeData.normalEdges := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hs => (Finset.mem_sdiff.mp he).2 ((hstrict e).mp hs)⟩
  refine directedFlipOfCovers hE
    (Fin.rev_lt_rev.mpr tbc.1) (Fin.rev_lt_rev.mpr sab.1)
    (ρ w.ebc) (ρ w.eab) (htail _) ?_ (htail _) (hhead _)
    (hnormal _ w.ebc_normal) (hnormal _ w.eab_normal)
    ((hcovers η b c).mpr tbc) ((hcovers η a c).mpr tac)
    (fun h => tnab ((hcovers η a b).mp h))
    ((hcovers θ a c).mpr sac) ((hcovers θ a b).mpr sab)
    (fun h => snbc ((hcovers θ b c).mp h)) ?_
  · exact (hhead _).trans (congrArg Fin.rev w.short_head_tail.symm)
  · intro e heab hebc
    obtain ⟨f, rfl⟩ := ρ.surjective e
    rw [reverseOrientation_mem, reverseOrientation_mem]
    exact (w.agree_elsewhere f (fun h => hebc (congrArg ρ h))
      (fun h => heab (congrArg ρ h))).symm

theorem reverseOrientation_flip (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev)
    {θ η : Orientation D} (h : Flip D θ η) :
    Flip E (reverseOrientation hE ρ hstrict θ) (reverseOrientation hE ρ hstrict η) := by
  rcases h with h | h
  · exact Or.inr ⟨reverseDirectedFlip hD hE ρ hstrict htail hhead h.some⟩
  · exact Or.inl ⟨reverseDirectedFlip hD hE ρ hstrict htail hhead h.some⟩

theorem reverseOrientation_reachable (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev)
    {θ η : Orientation D} (h : Relation.ReflTransGen (Flip D) θ η) :
    Relation.ReflTransGen (Flip E)
      (reverseOrientation hE ρ hstrict θ) (reverseOrientation hE ρ hstrict η) :=
  h.lift _ (fun _ _ hs => reverseOrientation_flip hD hE ρ hstrict htail hhead hs)

theorem reverseOrientation_reachable_iff (hD : Forward D) (hE : Forward E)
    (ρ : Edge D.area ≃ Edge E.area) (hstrict)
    (htail : ∀ e, (ρ e).tail = e.head.rev)
    (hhead : ∀ e, (ρ e).head = e.tail.rev) (θ η : Orientation D) :
    Relation.ReflTransGen (Flip E)
      (reverseOrientation hE ρ hstrict θ) (reverseOrientation hE ρ hstrict η) ↔
      Relation.ReflTransGen (Flip D) θ η := by
  have hs : ∀ e, ρ.symm e ∈ D.strict ↔ e ∈ E.strict := fun e => by
    simpa only [Equiv.apply_symm_apply] using (hstrict (ρ.symm e)).symm
  have ht : ∀ e, (ρ.symm e).tail = e.head.rev := fun e => by
    simpa only [Equiv.apply_symm_apply, Fin.rev_rev] using
      (congrArg Fin.rev (hhead (ρ.symm e))).symm
  have hh : ∀ e, (ρ.symm e).head = e.tail.rev := fun e => by
    simpa only [Equiv.apply_symm_apply, Fin.rev_rev] using
      (congrArg Fin.rev (htail (ρ.symm e))).symm
  constructor
  · intro h
    have hp := reverseOrientation_reachable hE hD ρ.symm hs ht hh h
    simpa only [reverseOrientation_inverse hD hE ρ hstrict hs] using hp
  · exact reverseOrientation_reachable hD hE ρ hstrict htail hhead

end

end VerticalStripLLT.Circular.DiagramProof

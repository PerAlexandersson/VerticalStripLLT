import VerticalStripLLT.Components.UndecoratedFlips
import VerticalStripLLT.Components.UndecoratedRecovery

/-! Forgetting strict markings preserves entire circular flip components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Circular

open Classical

variable {n : ℕ} {D : Diagram n}

namespace DirectedFlipWitness

/-- Reflect an undecorated witness between images of original orientations. -/
def ofUndecorated {θ η : Orientation D}
    (w : DirectedFlipWitness D.undecorated θ.toUndecorated η.toUndecorated) :
    DirectedFlipWitness D θ η where
  a := w.a
  b := w.b
  c := w.c
  cyclicWindow := w.cyclicWindow
  eab := w.eab
  ebc := w.ebc
  eab_normal := (w.undecorated_shorts_normal (D := D)).1
  ebc_normal := (w.undecorated_shorts_normal (D := D)).2
  ab_lift := w.ab_lift
  bc_lift := w.bc_lift
  source_ab := by rw [← θ.toUndecorated_liftCover]; exact w.source_ab
  source_ac := by rw [← θ.toUndecorated_liftCover]; exact w.source_ac
  source_not_bc := by rw [← θ.toUndecorated_liftCover]; exact w.source_not_bc
  target_ac := by rw [← η.toUndecorated_liftCover]; exact w.target_ac
  target_bc := by rw [← η.toUndecorated_liftCover]; exact w.target_bc
  target_not_ab := by rw [← η.toUndecorated_liftCover]; exact w.target_not_ab
  agree_elsewhere := by
    intro e hab hbc
    have h := w.agree_elsewhere e hab hbc
    change e ∈ D.strict ∪ θ.val ↔ e ∈ D.strict ∪ η.val at h
    by_cases hs : e ∈ D.strict
    · have hθ : e ∉ θ.val := fun he => (Finset.mem_sdiff.mp (θ.property.1 he)).2 hs
      have hη : e ∉ η.val := fun he => (Finset.mem_sdiff.mp (η.property.1 he)).2 hs
      simp [hθ, hη]
    · simpa only [Finset.mem_union, hs, false_or] using h

end DirectedFlipWitness

theorem flip_toUndecorated_iff {θ η : Orientation D} :
    Flip D.undecorated θ.toUndecorated η.toUndecorated ↔ Flip D θ η := by
  refine ⟨?_, flip_toUndecorated⟩
  intro h
  rcases h with h | h
  · exact Or.inl ⟨h.some.ofUndecorated⟩
  · exact Or.inr ⟨h.some.ofUndecorated⟩

/-- Every intermediate state of an undecorated path starting in the image can be recovered. -/
theorem exists_original_of_undecorated_reachable {θ : Orientation D}
    {α : Orientation D.undecorated}
    (h : Relation.ReflTransGen (Flip D.undecorated) θ.toUndecorated α) :
    ∃ η : Orientation D,
      Relation.ReflTransGen (Flip D) θ η ∧ η.toUndecorated = α := by
  induction h with
  | refl => exact ⟨θ, Relation.ReflTransGen.refl, rfl⟩
  | @tail α β hpath hs ih =>
    obtain ⟨η, hθη, rfl⟩ := ih
    have hstrict : D.strict ⊆ β.val :=
      (strict_subset_iff_of_undecorated_flip (D := D) hs).mp Finset.subset_union_left
    let ξ : Orientation D := β.fromUndecorated hstrict
    have hξ : ξ.toUndecorated = β := β.toUndecorated_fromUndecorated hstrict
    have hs' : Flip D η ξ := flip_toUndecorated_iff.mp (by rwa [hξ])
    exact ⟨ξ, hθη.tail hs', hξ⟩

theorem reachable_toUndecorated {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) :
    Relation.ReflTransGen (Flip D.undecorated) θ.toUndecorated η.toUndecorated :=
  h.lift Orientation.toUndecorated (fun _ _ hs => flip_toUndecorated hs)

/-- The original component maps onto an entire undecorated component, not merely a subset. -/
theorem flipComponent_toUndecorated (θ : Orientation D) :
    flipComponent D.undecorated θ.toUndecorated =
      (flipComponent D θ).image Orientation.toUndecorated := by
  ext α
  constructor
  · intro hα
    obtain ⟨η, hη, heq⟩ :=
      exists_original_of_undecorated_reachable (mem_flipComponent_iff.mp hα)
    exact Finset.mem_image.mpr ⟨η, mem_flipComponent_iff.mpr hη, heq⟩
  · intro hα
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hα
    exact mem_flipComponent_iff.mpr (reachable_toUndecorated (mem_flipComponent_iff.mp hη))

end VerticalStripLLT.Circular

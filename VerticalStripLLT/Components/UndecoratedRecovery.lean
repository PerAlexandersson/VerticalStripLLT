import VerticalStripLLT.Components.UndecoratedSelection

/-! Recovering decorated orientations from selections retaining the strict edges. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Circular.Orientation

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

private theorem strict_union_sdiff (α : Orientation D.undecorated)
    (hstrict : D.strict ⊆ α.val) : D.strict ∪ (α.val \ D.strict) = α.val := by
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff]
  grind

/-- Restore the original strict markings, deleting them from the normal selected set. -/
def fromUndecorated (α : Orientation D.undecorated) (hstrict : D.strict ⊆ α.val) :
    Orientation D := by
  refine ⟨α.val \ D.strict, ?_, ?_⟩
  · intro e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp he).2⟩
  · apply (D.undecorated_admissible_iff (α.val \ D.strict)).mp
    rw [strict_union_sdiff α hstrict]
    exact α.property.2

@[simp]
theorem fromUndecorated_val (α : Orientation D.undecorated) (hstrict : D.strict ⊆ α.val) :
    (α.fromUndecorated hstrict).val = α.val \ D.strict := rfl

@[simp]
theorem toUndecorated_fromUndecorated (α : Orientation D.undecorated)
    (hstrict : D.strict ⊆ α.val) :
    (α.fromUndecorated hstrict).toUndecorated = α := by
  apply Subtype.ext
  exact strict_union_sdiff α hstrict

@[simp]
theorem fromUndecorated_toUndecorated (θ : Orientation D)
    (hstrict : D.strict ⊆ θ.toUndecorated.val) :
    θ.toUndecorated.fromUndecorated hstrict = θ := by
  apply Subtype.ext
  change (D.strict ∪ θ.val) \ D.strict = θ.val
  ext e
  have hn : e ∈ θ.val → e ∉ D.strict := fun he =>
    (Finset.mem_sdiff.mp (θ.property.1 he)).2
  simp only [Finset.mem_sdiff, Finset.mem_union]
  grind

theorem toUndecorated_injective :
    Function.Injective (toUndecorated : Orientation D → Orientation D.undecorated) := by
  intro θ η h
  have hθ : D.strict ⊆ θ.toUndecorated.val := Finset.subset_union_left
  have hη : D.strict ⊆ η.toUndecorated.val := Finset.subset_union_left
  have hrec : θ.toUndecorated.fromUndecorated hθ =
      η.toUndecorated.fromUndecorated hη := by
    apply Subtype.ext
    exact congrArg (fun α : Orientation D.undecorated => α.val \ D.strict) h
  simpa only [fromUndecorated_toUndecorated] using hrec

end

end VerticalStripLLT.Circular.Orientation

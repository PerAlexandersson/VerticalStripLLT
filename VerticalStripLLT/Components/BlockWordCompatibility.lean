import VerticalStripLLT.Components.BlockExtractor

/-! Compatibility of concatenated and flattened words. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*}

/-- Compatibility of an append is internal compatibility plus the cross condition. -/
theorem wordCompatible_append_iff (R : V → V → Prop) (L M : List V) :
    wordCompatible R (L ++ M) ↔
      wordCompatible R L ∧ wordCompatible R M ∧
        ∀ u ∈ L, ∀ v ∈ M, ¬ R v u := by
  simp only [wordCompatible, List.pairwise_append]

/-- If every earlier block is compatible with every later block, compatibility of
the flattening is equivalent to compatibility inside every block. -/
theorem wordCompatible_flatten_iff
    (R : V → V → Prop) (blocks : List (List V))
    (hcross : blocks.Pairwise
      (fun L M => ∀ ⦃u v⦄, u ∈ L → v ∈ M → ¬ R v u)) :
    wordCompatible R blocks.flatten ↔
      ∀ L ∈ blocks, wordCompatible R L := by
  induction blocks with
  | nil => simp [wordCompatible]
  | cons L blocks ih =>
    have hcons := List.pairwise_cons.mp hcross
    rw [List.flatten_cons, wordCompatible_append_iff]
    constructor
    · rintro ⟨hL, hblocks, _⟩ M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hL
      · exact (ih hcons.2).mp hblocks M hM
    · intro hall
      have hL : wordCompatible R L := hall L (by simp)
      have hblocks :
          ∀ M ∈ blocks, wordCompatible R M := by
        intro M hM
        exact hall M (List.mem_cons_of_mem L hM)
      refine ⟨hL, (ih hcons.2).mpr hblocks, ?_⟩
      intro u hu v hv
      obtain ⟨M, hM, hvM⟩ := List.mem_flatten.mp hv
      exact hcons.1 M hM hu hvM

end

end VerticalStripLLT.Components

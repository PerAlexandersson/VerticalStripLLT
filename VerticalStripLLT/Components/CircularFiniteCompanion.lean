import VerticalStripLLT.Components.GainExpansion
import VerticalStripLLT.Components.CircularGainData
import VerticalStripLLT.Components.ColoringDeletion
import VerticalStripLLT.Components.HRVDeletion
import VerticalStripLLT.Components.UndecoratedSelection

/-! The finite companion expansions for the actual circular coloring and HRV semantics. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Circular.Orientation

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

theorem strictOrderEnumerator_companion_of_no_strict (θ : Orientation D)
    (hstrict : D.strict = ∅) (m : ℕ) :
    D.edgeData.strictOrderEnumerator θ.val m =
      ∑ F ∈ θ.val.powerset, D.naturalGain.coefficient θ.val F •
        D.edgeData.strictOrderEnumerator F m := by
  apply D.naturalGain.expansion_of_deletionRecurrence θ.val
    (fun X => D.edgeData.strictOrderEnumerator X m)
  · simpa only [hstrict, Finset.empty_union] using θ.naturalGain_selected_acyclic
  · intro X _ w
    apply D.edgeData.sum_powerset_strictOrderEnumerator_eq_zero
      (X \ w.optional) w.optional w.positive w.negative w.positive_ne_nil
      (fun e he => Finset.mem_union_right D.strict (w.positive_mem e he))
      w.negative_mem w.endpoint_perm m

/-- The entire integer HRV map satisfies the canonical balanced-subset expansion. -/
theorem liftedHRV_value_companion_of_no_strict {M : Type*} [AddCommGroup M]
    (θ : Orientation D) (hstrict : D.strict = ∅) (value : (ℤ → ℤ) → M) :
    value θ.liftedHRV = ∑ F ∈ θ.val.powerset,
      D.naturalGain.coefficient θ.val F • value (θ.subselection F).liftedHRV := by
  have hself : θ.subselection θ.val = θ := by
    apply Subtype.ext
    exact θ.val_subselection_eq θ.val Finset.Subset.rfl
  conv_lhs => rw [← hself]
  apply D.naturalGain.expansion_of_deletionRecurrence θ.val
    (fun X => value (θ.subselection X).liftedHRV)
  · simpa only [hstrict, Finset.empty_union] using θ.naturalGain_selected_acyclic
  · intro X hX w
    apply sum_powerset_liftedHRV_value_eq_zero (X \ w.optional) w.optional
      w.positive w.negative (fun J => θ.subselection ((X \ w.optional) ∪ J))
    · intro J hJ
      apply θ.val_subselection_eq
      exact (Finset.union_subset Finset.sdiff_subset (hJ.trans w.optional_subset)).trans hX
    · exact w.negative_mem
    · intro e he
      exact Finset.mem_union_right D.strict (w.positive_mem e he)
    · exact w.endpoint_perm
    · exact w.excess

/-- The coloring companion permits deletions of originally strict edges by first
moving every selected edge into the same-area undecorated graph. -/
theorem strictOrderEnumerator_finiteCompanion (θ : Orientation D) (m : ℕ) :
    D.edgeData.strictOrderEnumerator θ.val m =
      ∑ F ∈ (D.strict ∪ θ.val).powerset,
        D.naturalGain.coefficient (D.strict ∪ θ.val) F •
          D.undecorated.edgeData.strictOrderEnumerator F m := by
  have h := θ.toUndecorated.strictOrderEnumerator_companion_of_no_strict rfl m
  rw [θ.toUndecorated_strictOrderEnumerator] at h
  simp only [toUndecorated_val, Diagram.naturalGain] at h
  convert h using 1 <;> congr 1

/-- The finite companion before evaluating the entire periodic HRV map. -/
theorem liftedHRV_value_finiteCompanion {M : Type*} [AddCommGroup M]
    (θ : Orientation D) (value : (ℤ → ℤ) → M) :
    value θ.liftedHRV =
      ∑ F ∈ (D.strict ∪ θ.val).powerset,
        D.naturalGain.coefficient (D.strict ∪ θ.val) F •
          value (θ.toUndecorated.subselection F).liftedHRV := by
  have h := θ.toUndecorated.liftedHRV_value_companion_of_no_strict rfl value
  have heq : θ.toUndecorated.liftedHRV = θ.liftedHRV :=
    funext θ.toUndecorated_liftedHRV
  rw [heq] at h
  simp only [toUndecorated_val, Diagram.naturalGain] at h
  convert h using 1 <;> congr 1

end

end VerticalStripLLT.Circular.Orientation

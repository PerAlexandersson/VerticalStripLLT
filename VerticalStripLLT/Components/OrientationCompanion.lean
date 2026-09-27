import VerticalStripLLT.Components.CircularFiniteCompanion
import VerticalStripLLT.Components.OrientationSubsetSum

/-! Orientation-indexed forms of the finite companion identities. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The coefficient-weighted subset sum can be reindexed by orientations. -/
theorem sum_coefficient_subselection {M : Type*} [AddCommGroup M]
    (α : Orientation D) (value : Orientation D → M) :
    (∑ F ∈ α.val.powerset,
      D.naturalGain.coefficient α.val F • value (α.subselection F)) =
      ∑ η : Orientation D,
        D.naturalGain.coefficient α.val η.val • value η := by
  calc
    (∑ F ∈ α.val.powerset,
        D.naturalGain.coefficient α.val F • value (α.subselection F)) =
        ∑ η : Orientation D,
          if η.val ⊆ α.val then
            D.naturalGain.coefficient α.val η.val • value η
          else 0 :=
      sum_powerset_subselection α
        (fun F η => D.naturalGain.coefficient α.val F • value η)
    _ = ∑ η : Orientation D,
        D.naturalGain.coefficient α.val η.val • value η := by
      apply Finset.sum_congr rfl
      intro η hη
      by_cases hsub : η.val ⊆ α.val
      · simp [hsub]
      · rw [D.naturalGain.coefficient_eq_zero_of_not_subset hsub, zero_smul]
        simp [hsub]

/-- In the no-strict case, the HRV companion sum may be indexed by all
orientations, with the full coefficient notation used by component formulas. -/
theorem liftedHRV_value_companion_all_of_no_strict {M : Type*} [AddCommGroup M]
    (α : Orientation D) (hstrict : D.strict = ∅)
    (value : (ℤ → ℤ) → M) :
    value α.liftedHRV =
      ∑ η : Orientation D,
        D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) •
          value η.liftedHRV := by
  have hcomp := α.liftedHRV_value_companion_of_no_strict hstrict value
  have hsum := α.sum_coefficient_subselection (fun η => value η.liftedHRV)
  calc
    value α.liftedHRV =
        ∑ F ∈ α.val.powerset,
          D.naturalGain.coefficient α.val F •
            value (α.subselection F).liftedHRV := hcomp
    _ = ∑ η : Orientation D,
        D.naturalGain.coefficient α.val η.val • value η.liftedHRV := hsum
    _ = ∑ η : Orientation D,
        D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) •
          value η.liftedHRV := by
      simp [hstrict]

/-- The analogous all-orientation form for the strict-order enumerator. -/
theorem strictOrderEnumerator_companion_all_of_no_strict
    (α : Orientation D) (hstrict : D.strict = ∅) (m : ℕ) :
    D.edgeData.strictOrderEnumerator α.val m =
      ∑ η : Orientation D,
        D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) •
          D.edgeData.strictOrderEnumerator η.val m := by
  have hcomp := α.strictOrderEnumerator_companion_of_no_strict hstrict m
  have hsum := α.sum_coefficient_subselection
    (fun η => D.edgeData.strictOrderEnumerator η.val m)
  calc
    D.edgeData.strictOrderEnumerator α.val m =
        ∑ F ∈ α.val.powerset,
          D.naturalGain.coefficient α.val F •
            D.edgeData.strictOrderEnumerator F m := hcomp
    _ = ∑ F ∈ α.val.powerset,
          D.naturalGain.coefficient α.val F •
            D.edgeData.strictOrderEnumerator (α.subselection F).val m := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [α.val_subselection_eq F (Finset.mem_powerset.mp hF)]
    _ = ∑ η : Orientation D,
        D.naturalGain.coefficient α.val η.val •
          D.edgeData.strictOrderEnumerator η.val m := hsum
    _ = ∑ η : Orientation D,
        D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val) •
          D.edgeData.strictOrderEnumerator η.val m := by
      simp [hstrict]

end

end VerticalStripLLT.Circular.Orientation

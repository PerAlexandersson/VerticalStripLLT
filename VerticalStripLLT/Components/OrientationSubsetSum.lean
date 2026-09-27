import VerticalStripLLT.Components.CircularGainData

/-! Reindexing an orientation sum by all subsets of one orientation. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Restricting one orientation to all subsets of its selected edge set
reindexes the finite orientation sum. -/
theorem sum_powerset_subselection {M : Type*} [AddCommMonoid M]
    (α : Orientation D)
    (f : Finset (Edge D.area) → Orientation D → M) :
    (∑ F ∈ α.val.powerset, f F (α.subselection F)) =
      ∑ η : Orientation D,
        if η.val ⊆ α.val then f η.val η else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun F _ => α.subselection F) ?_ ?_ ?_ ?_
  · intro F hF
    have hFsub : F ⊆ α.val := Finset.mem_powerset.mp hF
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [α.val_subselection_eq F hFsub]
    exact hFsub
  · intro F hF G hG hEq
    have hFsub : F ⊆ α.val := Finset.mem_powerset.mp hF
    have hGsub : G ⊆ α.val := Finset.mem_powerset.mp hG
    have hVal := congrArg Subtype.val hEq
    rw [α.val_subselection_eq F hFsub, α.val_subselection_eq G hGsub] at hVal
    exact hVal
  · intro η hη
    have hηsub : η.val ⊆ α.val := (Finset.mem_filter.mp hη).2
    refine ⟨η.val, Finset.mem_powerset.mpr hηsub, ?_⟩
    apply Subtype.ext
    exact α.val_subselection_eq η.val hηsub
  · intro F hF
    rw [α.val_subselection_eq F (Finset.mem_powerset.mp hF)]

end

end VerticalStripLLT.Circular.Orientation

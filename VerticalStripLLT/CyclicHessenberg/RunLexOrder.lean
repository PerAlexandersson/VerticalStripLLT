import VerticalStripLLT.CyclicHessenberg.ColorRuns
import VerticalStripLLT.CyclicHessenberg.CompositionSplit

set_option autoImplicit false

/-! The structural run decomposition used for the sorted-loop order bridge. -/

namespace List

variable {C A : Type*} [LinearOrder C] [LinearOrder A]

/-- Colors increase lexicographically, with labels decreasing within a color. -/
def RunLexOrder (x y : C × A) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)

/-- A constant color block contributes exactly the decreasing-label order. -/
theorem pairwise_zip_replicate_iff (c : C) (l : List A) :
    ((List.replicate l.length c).zip l).Pairwise RunLexOrder ↔
      l.Pairwise (· > ·) := by
  have hzip : (List.replicate l.length c).zip l = l.map fun a => (c, a) := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.replicate_succ, ih]
  rw [hzip, List.pairwise_map]
  simp [RunLexOrder]

/-- If composition block sizes are the equality-run lengths, splitting recovers the runs. -/
theorem splitWrtComposition_eq_equalityRuns (colors : List C)
    (β : Composition colors.length)
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    colors.splitWrtComposition β = equalityRuns colors := by
  apply List.splitWrtComposition_eq_of_flatten_eq β rfl
    (equalityRuns colors)
  · exact List.flatten_splitBy _ _
  · exact hblocks.symm

/-- The paired blocks are the zips of the color runs and label blocks. -/
theorem splitWrtComposition_zip_eq_runs (colors : List C) (labels : List A)
    (β : Composition colors.length)
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    (colors.zip labels).splitWrtComposition β =
      (equalityRuns colors).zipWith List.zip (labels.splitWrtComposition β) := by
  rw [List.splitWrtComposition_zip, splitWrtComposition_eq_equalityRuns _ β hblocks]

end List

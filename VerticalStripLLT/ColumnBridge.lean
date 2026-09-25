import VerticalStripLLT.OrientationColumn
import VerticalStripLLT.ColumnBase

/-! Uniform column bridge between the orientation model and coloring semantics.

This is the finite column family for every `k` and alphabet size `m`; it is
not a general LLT expansion theorem.
-/

namespace VerticalStripLLT

theorem orientationExpansion_column (k : ℕ) :
    orientationExpansion (SchroderPath.column k) = elementary k.succPNat := by
  simpa [orientationExpansion] using orientationExpansionAt_column k (Polynomial.X - 1)

theorem shiftedOrientationExpansion_column (k : ℕ) :
    shiftedOrientationExpansion (SchroderPath.column k) = elementary k.succPNat := by
  simpa [shiftedOrientationExpansion] using orientationExpansionAt_column k Polynomial.X

theorem coloringLLT_column_eq_eval_orientationExpansion (k m : ℕ) :
    coloringLLT (SchroderPath.column k) m =
      evalElementary m (orientationExpansion (SchroderPath.column k)) := by
  rw [orientationExpansion_column, coloringLLT_column_eq_evalElementary]

end VerticalStripLLT

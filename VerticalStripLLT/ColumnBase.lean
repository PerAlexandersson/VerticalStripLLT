import VerticalStripLLT.Column
import VerticalStripLLT.ElementaryColorings
import Mathlib.Data.PNat.Defs

/-! The general initial condition in Theorem `recursion` and Proposition
`coloringProperties` of the manuscript, for every finite alphabet. -/

namespace VerticalStripLLT

open scoped BigOperators

theorem coloringLLT_column (k m : ℕ) :
    coloringLLT (SchroderPath.column k) m =
      MvPolynomial.esymm (Fin m) Q (k + 1) := by
  classical
  rw [coloringLLT]
  calc
    (∑ c : Fin (k + 1) → Fin m, coloringWeight (SchroderPath.column k) c) =
        ∑ c : Fin (k + 1) → Fin m,
          if StrictMono c then ∏ i, MvPolynomial.X (c i) else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [coloringWeight, SchroderPath.admissible_column_iff,
        SchroderPath.column_ascentCount]
    _ = increasingColoringSum (k + 1) m := by rfl
    _ = MvPolynomial.esymm (Fin m) Q (k + 1) :=
      increasingColoringSum_eq_esymm (k + 1) m

theorem coloringLLT_column_eq_evalElementary (k m : ℕ) :
    coloringLLT (SchroderPath.column k) m =
      evalElementary m (elementary k.succPNat) := by
  rw [evalElementary_elementary]
  exact coloringLLT_column k m

end VerticalStripLLT

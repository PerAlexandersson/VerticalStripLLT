import VerticalStripLLT.CyclicHessenberg.Layer

set_option autoImplicit false

/-! Sum and spectator lemmas for the adjacent layer-exchange argument. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- The layer ascent count as a sum of event indicators over ordered positions. -/
theorem layerAscentCount_eq_sum {k : ℕ} (h : Hessenberg k)
    (π τ : FullOrder k) :
    layerAscentCount h π τ =
      ∑ p : LayerPosition k, ∑ q : LayerPosition k,
        if p < q ∧ (orderEquiv π p).val < (orderEquiv π q).val ∧
            (orderEquiv π q).val ≤ h (orderEquiv τ p).val then 1 else 0 := by
  classical
  rw [layerAscentCount, layerAscentEvents]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Finset.sum_univ]
  rw [Fintype.sum_prod_type]

/-- The two later-spectator contributions are invariant under the adjacent exchange. -/
theorem laterSpectatorIndicatorSwap {V : Type*} [LinearOrder V]
    {a b C D v : V} (hab : a < b) (hbc : b ≤ C) (hCD : C ≤ D) :
    (if a < v ∧ v ≤ C then 1 else 0) + (if b < v ∧ v ≤ D then 1 else 0) =
      (if b < v ∧ v ≤ C then 1 else 0) + (if a < v ∧ v ≤ D then 1 else 0) := by
  by_cases hva : v ≤ a
  · have hav : ¬ a < v := not_lt.mpr hva
    have hbv : ¬ b < v := not_lt.mpr (le_trans hva hab.le)
    simp [hav, hbv]
  · have hav : a < v := lt_of_not_ge hva
    by_cases hvb : v ≤ b
    · have hbv : ¬ b < v := not_lt.mpr hvb
      have hvC : v ≤ C := hvb.trans hbc
      have hvD : v ≤ D := hvC.trans hCD
      simp [hav, hbv, hvC, hvD]
    · have hbv : b < v := lt_of_not_ge hvb
      by_cases hvC : v ≤ C
      · have hvD : v ≤ D := hvC.trans hCD
        simp [hav, hbv, hvC, hvD]
      · by_cases hvD : v ≤ D
        · simp [hav, hbv, hvC, hvD]
        · simp [hav, hbv, hvC, hvD]

end VerticalStripLLT.CyclicHessenberg

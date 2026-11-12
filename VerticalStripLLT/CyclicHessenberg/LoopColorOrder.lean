import VerticalStripLLT.CyclicHessenberg.Coloring
import VerticalStripLLT.CyclicHessenberg.LoopKernel

set_option autoImplicit false

/-! Identify the loop color/tie relation with positions in its sorted order. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- The full boundary order sorted by color and decreasing vertex within a color. -/
noncomputable def colorSortedFullOrder {k m : ℕ} (κ : Fin k → Fin m) : FullOrder k :=
  sortColorOrder (fun v : (Finset.univ : Finset (Fin k)) => κ v.val)

/-- The permutation of the vertices obtained by reading the sorted full order. -/
noncomputable def colorSortedPerm {k m : ℕ} (κ : Fin k → Fin m) : Equiv.Perm (Fin k) :=
  fullOrdersPerm k (colorSortedFullOrder κ)

private theorem loopColorPrecedes_asymm {k m : ℕ} (κ : Fin k → Fin m)
    {a b : Fin k} (hab : colorPrecedes κ a b) (hba : colorPrecedes κ b a) : False := by
  rcases hab with hab | ⟨hab, hab'⟩
  · rcases hba with hba | ⟨hba, hba'⟩
    · exact (lt_asymm hab hba).elim
    · rw [hba] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨hba, hba'⟩
    · rw [← hab] at hba
      exact (lt_irrefl _ hba).elim
    · exact (lt_asymm hab' hba').elim

/-- Every pair of positions in the sorted order satisfies the loop color relation. -/
theorem colorSortedPerm_precedes_of_lt {k m : ℕ} (κ : Fin k → Fin m)
    {i j : Fin k} (hij : i < j) :
    colorPrecedes κ (colorSortedPerm κ i) (colorSortedPerm κ j) := by
  let i' : LayerPosition k := (layerPositionEquiv k).symm i
  let j' : LayerPosition k := (layerPositionEquiv k).symm j
  have hij' : i' < j' := by
    change i.val < j.val
    exact hij
  have hsorted := sortColorOrder_orderEquiv_precedes
    (κ := fun v : (Finset.univ : Finset (Fin k)) => κ v.val) hij'
  have hpi : colorSortedPerm κ i =
      (orderEquiv (colorSortedFullOrder κ) i').val := by
    simpa [colorSortedPerm, colorSortedFullOrder, i'] using
      (fullOrdersPerm_apply_position (colorSortedFullOrder κ) i')
  have hpj : colorSortedPerm κ j =
      (orderEquiv (colorSortedFullOrder κ) j').val := by
    simpa [colorSortedPerm, colorSortedFullOrder, j'] using
      (fullOrdersPerm_apply_position (colorSortedFullOrder κ) j')
  rw [hpi, hpj]
  simpa [fiberColorPrecedes, colorPrecedes, colorSortedFullOrder] using hsorted

/-- Positions increase exactly when their sorted vertices satisfy `colorPrecedes`. -/
theorem colorSortedPerm_precedes_iff_lt {k m : ℕ} (κ : Fin k → Fin m)
    (i j : Fin k) :
    i < j ↔ colorPrecedes κ (colorSortedPerm κ i) (colorSortedPerm κ j) := by
  constructor
  · exact colorSortedPerm_precedes_of_lt κ
  · intro h
    rcases lt_trichotomy i j with hij | hij | hji
    · exact hij
    · subst j
      exact False.elim (loopColorPrecedes_asymm κ h h)
    · exact False.elim (loopColorPrecedes_asymm κ h
        (colorSortedPerm_precedes_of_lt κ hji))

end VerticalStripLLT.CyclicHessenberg

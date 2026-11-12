import VerticalStripLLT.CyclicHessenberg.LoopColorOrder
import VerticalStripLLT.CyclicHessenberg.LayerExchangeCounts

/-! The cover/path bijection preserves individual ascent events, including their layer labels. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n m : ℕ}

noncomputable def colorSortedPositions (κ : Fin k → Fin m) : LayerPosition k ≃ Fin k :=
  (layerPositionEquiv k).trans (colorSortedPerm κ)

@[simp] theorem colorSortedPositions_apply (κ : Fin k → Fin m) (i : LayerPosition k) :
    colorSortedPositions κ i = (orderEquiv (colorSortedFullOrder κ) i).val :=
  fullOrdersPerm_apply_position (colorSortedFullOrder κ) i

theorem colorSortedPositions_precedes (κ : Fin k → Fin m) (i j : LayerPosition k) :
    i < j ↔ colorPrecedes κ (colorSortedPositions κ i) (colorSortedPositions κ j) := by
  have h := colorSortedPerm_precedes_iff_lt κ (layerPositionEquiv k i) (layerPositionEquiv k j)
  exact h

/-- Ascent events of an ordered boundary path retain their layer and both positions. -/
noncomputable def pathAscentEvents (h : Tuple k n) {π : FullOrder k}
    (P : ClosedLayerPath h π) : Finset (Fin n × LayerPosition k × LayerPosition k) := by
  classical
  exact Finset.univ.filter fun e =>
    e.2.1 < e.2.2 ∧
      (orderEquiv (P.val e.1.castSucc) e.2.1).val <
        (orderEquiv (P.val e.1.castSucc) e.2.2).val ∧
      (orderEquiv (P.val e.1.castSucc) e.2.2).val ≤
        h e.1 (orderEquiv (P.val e.1.succ) e.2.1).val

theorem pathAscentEvents_card (h : Tuple k n) {π : FullOrder k}
    (P : ClosedLayerPath h π) :
    (pathAscentEvents h P).card =
      ∑ ℓ : Fin n, layerAscentCount (h ℓ) (P.val ℓ.castSucc) (P.val ℓ.succ) := by
  classical
  simp only [pathAscentEvents, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, layerAscentCount_eq_sum]

/-- Reindex positions by the canonical first-layer label of each loop. -/
noncomputable def loopEventEquiv (κ : Fin k → Fin m) :
    (Fin n × LayerPosition k × LayerPosition k) ≃ (Fin n × Fin k × Fin k) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (colorSortedPositions κ) (colorSortedPositions κ))

/-- The colored events in the independently defined loop polynomial. -/
noncomputable def coloredLoopEvents (h : Tuple k n) (L : LoopCover h)
    (κ : Fin k → Fin m) : Finset (Fin n × Fin k × Fin k) := by
  classical
  exact (loopAscentEvents h L).filter (fun x => colorPrecedes κ x.2.1 x.2.2)

theorem loopEventEquiv_mem (h : Tuple k n) (L : LoopCover h) (κ : Fin k → Fin m)
    (e : Fin n × LayerPosition k × LayerPosition k) :
    e ∈ pathAscentEvents h (loopToBoundaryPath h (colorSortedFullOrder κ) L) ↔
      loopEventEquiv κ e ∈ coloredLoopEvents h L κ := by
  classical
  rcases e with ⟨ℓ, i, j⟩
  simp only [pathAscentEvents, coloredLoopEvents, Finset.mem_filter, Finset.mem_univ, true_and,
    loopToBoundaryPath_position, loopAscentEvents, loopEventEquiv, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, colorSortedPositions_apply]
  have hp := colorSortedPositions_precedes κ i j
  simp only [colorSortedPositions_apply] at hp
  rw [hp]
  tauto

/-- Equality of the original colored ascent count and the sum of transfer-layer exponents. -/
theorem coloredLoopAscentCount_eq_path_sum (h : Tuple k n) (L : LoopCover h)
    (κ : Fin k → Fin m) :
    coloredLoopAscentCount h L κ =
      ∑ ℓ : Fin n, layerAscentCount (h ℓ)
        ((loopToBoundaryPath h (colorSortedFullOrder κ) L).val ℓ.castSucc)
        ((loopToBoundaryPath h (colorSortedFullOrder κ) L).val ℓ.succ) := by
  classical
  rw [← pathAscentEvents_card]
  exact (Finset.card_equiv (loopEventEquiv κ) (loopEventEquiv_mem h L κ)).symm

end VerticalStripLLT.CyclicHessenberg

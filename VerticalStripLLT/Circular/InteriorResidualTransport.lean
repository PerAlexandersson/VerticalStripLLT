import VerticalStripLLT.Circular.InteriorResidualPairs
import VerticalStripLLT.Circular.InteriorReversalSinkOrder
import VerticalStripLLT.Circular.OrientationSumConjugacy

/-! Coloring and HRV transport after removing internal normal edges. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

private theorem liftStep_edgesOfPairs_iff_or (D : Diagram n)
    (A : Finset (Fin n × Fin n)) (x y : ℤ) :
    D.liftStep (D.edgesOfPairs A) x y ↔ D.liftStep ∅ x y ∨
      (D.boundaryNaturalLift x y ∧ (D.residue x, D.residue y) ∈ A) := by
  rw [D.liftStep_edgesOfPairs_iff, D.liftStep_empty_iff_strictAt_boundary]
  unfold boundaryNaturalLift
  constructor
  · rintro (⟨hs, hb⟩ | ⟨hb, hlt, hm⟩)
    · exact Or.inl ⟨hs, hb.symm⟩
    · exact Or.inr ⟨⟨hb, hlt⟩, hm⟩
  · rintro (⟨hs, hb⟩ | ⟨⟨hb, hlt⟩, hm⟩)
    · exact Or.inl ⟨hs, hb.symm⟩
    · exact Or.inr ⟨hb, hlt, hm⟩

namespace InteriorMergedComponent

variable {r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

/-- Every selection of exterior normal pairs has exactly its transported lifted graph. -/
theorem liftStep_exterior_reversal_iff (A : Finset (Fin n × Fin n))
    (hA : A ⊆ D.exteriorNormalPairs K.componentVertices) (x y : ℤ) :
    K.reversalTarget.liftStep
      (K.reversalTarget.edgesOfPairs
        (A.map (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding))
      (K.reversalLift x) (K.reversalLift y) ↔ D.liftStep (D.edgesOfPairs A) x y := by
  have hm : (K.reversalTarget.residue (K.reversalLift x),
      K.reversalTarget.residue (K.reversalLift y)) ∈
      A.map (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding ↔
        (D.residue x, D.residue y) ∈ A := by
    rw [K.reversalLift_residue, K.reversalLift_residue]
    exact Finset.mem_map' (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding
      (a := (D.residue x, D.residue y)) (s := A)
  rw [liftStep_edgesOfPairs_iff_or, liftStep_edgesOfPairs_iff_or,
    K.liftStep_empty_reversal_iff, hm]
  by_cases ha : (D.residue x, D.residue y) ∈ A
  · have hout := (Finset.mem_filter.mp (hA ha)).2
    rw [K.boundaryNaturalLift_reversal_iff x y hout]
  · simp only [ha, and_false, or_false]

/-- Actual HRV sums over the exterior normal selections agree under column reversal. -/
theorem orientSum_exterior_reversal :
    D.orientSum (D.edgesOfPairs (D.exteriorNormalPairs K.componentVertices)) =
      K.reversalTarget.orientSum
        (K.reversalTarget.edgesOfPairs
          (K.reversalTarget.exteriorNormalPairs K.componentVertices)) := by
  have hR := D.exteriorNormalPairs_subset_normal K.componentVertices
  have hR' : (D.exteriorNormalPairs K.componentVertices).map
      (Equiv.prodCongr K.reversalPerm K.reversalPerm).toEmbedding ⊆
        K.reversalTarget.pairGraph.normalEdges := by
    rw [← K.exteriorNormalPairs_eq_map]
    exact K.reversalTarget.exteriorNormalPairs_subset_normal K.componentVertices
  have h := Diagram.orientSum_conjugate (D := D) (Q := K.reversalTarget)
    K.reversalPerm K.reversalLift (D.exteriorNormalPairs K.componentVertices) hR hR'
    K.reversalLift_residue
    (fun A hA x y => (K.liftStep_exterior_reversal_iff A hA x y).symm)
    (fun A _ x y hx hy hxy => K.reversalLift_order_sinks (D.edgesOfPairs A) x y hx hy hxy)
  rwa [← K.exteriorNormalPairs_eq_map] at h

/-- Actual coloring sums of the residual graphs agree under column reversal. -/
theorem coloringLLT_exterior_reversal (m : ℕ) :
    (⟨K.reversalTarget.exteriorNormalPairs K.componentVertices,
      K.reversalTarget.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m =
    (⟨D.exteriorNormalPairs K.componentVertices,
      D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m := by
  rw [K.exteriorNormalPairs_eq_map, K.strictPairs_eq_map]
  exact PairGraph.coloringLLT_relabel K.reversalPerm _ _

end InteriorMergedComponent
end VerticalStripLLT.Circular.Diagram

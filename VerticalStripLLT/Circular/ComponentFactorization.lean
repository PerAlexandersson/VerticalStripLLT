import VerticalStripLLT.Circular.InteriorResidualPairs
import VerticalStripLLT.Circular.AliasReductionOrient
import VerticalStripLLT.Circular.ForcedReduction

/-! Common forced factors for normal edges internal to a strictly ordered component. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n) (C : Finset (Fin n))

/-- Internal normal edges forced forward by the strict graph. -/
noncomputable def internalForwardPairs : Finset (Fin n × Fin n) :=
  D.pairGraph.normalEdges.filter fun p => p.1 ∈ C ∧ p.2 ∈ C ∧
    Relation.TransGen (D.edgeData.selected ∅) p.1 p.2

/-- The other internal normal edges, after removing forward and exterior pairs. -/
noncomputable def internalBackwardPairs : Finset (Fin n × Fin n) :=
  (D.pairGraph.normalEdges \ D.internalForwardPairs C) \ D.exteriorNormalPairs C

theorem internalForwardPairs_subset : D.internalForwardPairs C ⊆ D.pairGraph.normalEdges :=
  Finset.filter_subset _ _

theorem internalBackwardPairs_subset :
    D.internalBackwardPairs C ⊆ D.pairGraph.normalEdges \ D.internalForwardPairs C :=
  Finset.sdiff_subset

theorem normalPairs_erase_internal :
    (D.pairGraph.normalEdges \ D.internalForwardPairs C) \ D.internalBackwardPairs C =
      D.exteriorNormalPairs C := by
  ext p
  simp only [internalForwardPairs, internalBackwardPairs, exteriorNormalPairs,
    Finset.mem_sdiff, Finset.mem_filter]
  tauto

theorem internalForwardPairs_path (p : Fin n × Fin n) (hp : p ∈ D.internalForwardPairs C) :
    Relation.TransGen (D.edgeData.selected ∅) p.1 p.2 :=
  (Finset.mem_filter.mp hp).2.2.2

variable (htotal : ∀ u ∈ C, ∀ v ∈ C, u ≠ v →
  Relation.TransGen (D.edgeData.selected ∅) u v ∨
    Relation.TransGen (D.edgeData.selected ∅) v u)

include htotal in
theorem internalBackwardPairs_path (p : Fin n × Fin n) (hp : p ∈ D.internalBackwardPairs C) :
    Relation.TransGen (D.edgeData.selected ∅) p.2 p.1 := by
  obtain ⟨⟨hN, hF⟩, hR⟩ := Finset.mem_sdiff.mp hp |>.imp_left Finset.mem_sdiff.mp
  have hC : p.1 ∈ C ∧ p.2 ∈ C := by
    simpa only [exteriorNormalPairs, Finset.mem_filter, hN, true_and, not_or, not_not] using hR
  have hnot : ¬ Relation.TransGen (D.edgeData.selected ∅) p.1 p.2 := by
    intro h
    exact hF (Finset.mem_filter.mpr ⟨hN, hC.1, hC.2, h⟩)
  have hne : p.1 ≠ p.2 := by
    obtain ⟨e, _, heq⟩ := (D.mem_pairGraph_normal_iff p).mp hN
    rw [← heq]
    exact e.tail_ne_head
  exact (htotal p.1 hC.1 p.2 hC.2 hne).resolve_left hnot

include htotal in
/-- The unshifted coloring polynomial factors over the exact exterior residual graph. -/
theorem coloringLLT_component_factor (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X ^ (D.internalForwardPairs C).card *
      (⟨D.exteriorNormalPairs C, D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m := by
  rw [← D.pairGraph_coloringLLT m]
  rw [PairGraph.coloringLLT_erase_forced_set D.pairGraph (D.internalForwardPairs C)
    (D.internalForwardPairs_subset C) (fun p hp =>
      Relation.TransGen.mono
        (fun u v h => (D.selected_empty_iff_pair_strict u v).mp h) _ _
        (D.internalForwardPairs_path C p hp))]
  rw [PairGraph.coloringLLT_erase_descent_set
    (⟨D.pairGraph.normalEdges \ D.internalForwardPairs C, D.pairGraph.strictEdges⟩ : PairGraph n)
    (D.internalBackwardPairs C) (fun p hp =>
      Relation.TransGen.mono
        (fun u v h => (D.selected_empty_iff_pair_strict u v).mp h) _ _
        (D.internalBackwardPairs_path C htotal p hp))]
  rw [D.normalPairs_erase_internal C]

theorem edgesOfPairs_sdiff (A B : Finset (Fin n × Fin n)) :
    D.edgesOfPairs (A \ B) = D.edgesOfPairs A \ D.edgesOfPairs B := by
  ext e
  simp only [D.mem_edgesOfPairs, Finset.mem_sdiff]

theorem edgesOfPairs_normal : D.edgesOfPairs D.pairGraph.normalEdges = D.edgeData.normalEdges :=
  D.edgesOfPairs_map D.edgeData.normalEdges

include htotal in
/-- The HRV sum has the same forced-edge count as the coloring factorization. -/
theorem shiftedOrientationExpansion_component_factor :
    shiftedOrientationExpansion D =
      MvPolynomial.C (Polynomial.X + 1) ^ (D.internalForwardPairs C).card *
        D.orientSum (D.edgesOfPairs (D.exteriorNormalPairs C)) := by
  have hF := D.edgesOfPairs_sub_normal (D.internalForwardPairs_subset C)
  have hB : D.edgesOfPairs (D.internalBackwardPairs C) ⊆
      D.edgeData.normalEdges \ D.edgesOfPairs (D.internalForwardPairs C) := by
    have h := D.edgesOfPairs_mono (D.internalBackwardPairs_subset C)
    rwa [D.edgesOfPairs_sdiff, D.edgesOfPairs_normal] at h
  rw [D.shiftedOrientationExpansion_eq_orientSum,
    D.orientSum_forced_set _ _ (Finset.Subset.refl _) hF
      (fun e he => D.internalForwardPairs_path C (e.tail, e.head)
        ((D.mem_edgesOfPairs _ e).mp he)),
    D.orientSum_descent_set _ _ hB
      (fun e he => D.internalBackwardPairs_path C htotal (e.tail, e.head)
        ((D.mem_edgesOfPairs _ e).mp he)),
    D.card_edgesOfPairs (D.internalForwardPairs_subset C)]
  have hremain : (D.edgeData.normalEdges \ D.edgesOfPairs (D.internalForwardPairs C)) \
      D.edgesOfPairs (D.internalBackwardPairs C) = D.edgesOfPairs (D.exteriorNormalPairs C) := by
    rw [← D.edgesOfPairs_normal, ← D.edgesOfPairs_sdiff, ← D.edgesOfPairs_sdiff,
      D.normalPairs_erase_internal C]
  rw [hremain]

include htotal in
/-- After the q+1 substitution, both actual models have precisely the same scalar factor. -/
theorem xQShift_coloringLLT_component_factor (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      MvPolynomial.C (Polynomial.X + 1) ^ (D.internalForwardPairs C).card *
        xQShift m
          ((⟨D.exteriorNormalPairs C, D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m) := by
  rw [D.coloringLLT_component_factor C htotal m, map_mul, ← map_pow, xQShift_C_X_pow',
    map_pow]

include htotal in
/-- Internal comparability reduces the full bridge to the independently defined residual sums. -/
theorem expansion_iff_component_residual (m : ℕ) :
    (xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D)) ↔
      xQShift m ((⟨D.exteriorNormalPairs C, D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m) =
        evalElementary m (D.orientSum (D.edgesOfPairs (D.exteriorNormalPairs C))) := by
  rw [D.xQShift_coloringLLT_component_factor C htotal m,
    D.shiftedOrientationExpansion_component_factor C htotal, map_mul, map_pow, evalElementary_C]
  have hbase : (MvPolynomial.C (Polynomial.X + 1) : XPoly m) ≠ 0 := by
    intro h
    have hp : (Polynomial.X + 1 : Polynomial ℤ) = 0 :=
      MvPolynomial.C_injective (Fin m) (Polynomial ℤ) (by simpa only [map_zero] using h)
    have hv := congrArg (Polynomial.eval (0 : ℤ)) hp
    norm_num at hv
  exact ⟨mul_left_cancel₀ (pow_ne_zero _ hbase), congrArg (fun z =>
    (MvPolynomial.C (Polynomial.X + 1) : XPoly m) ^ (D.internalForwardPairs C).card * z)⟩

end VerticalStripLLT.Circular.Diagram

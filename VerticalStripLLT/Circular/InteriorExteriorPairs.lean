import VerticalStripLLT.Circular.InteriorExteriorBoundary
import VerticalStripLLT.Circular.NaturalPairSwap
import VerticalStripLLT.Circular.HRVRoots

/-! Actual finite natural and normal edge transport outside the reversed component. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem mem_naturalPairs_iff_lifts (D : Diagram n) (u v : Fin n) :
    (u, v) ∈ D.naturalPairs ↔
      ∃ x y : ℤ, D.residue x = u ∧ D.residue y = v ∧ D.boundaryNaturalLift x y := by
  rw [D.mem_naturalPairs_iff]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨hu, hv⟩ := Prod.mk.inj he
    have hx := Orientation.residue_intCast_eq (D := D) e.tail
    have hy := D.residue_add_length e (e.tail.val : ℤ) hx
    refine ⟨e.tail.val, (e.tail.val : ℤ) + e.length.val, hx.trans hu, hy.trans hv, ?_⟩
    exact D.boundaryNaturalLift_of_edge hy.symm (by ring)
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨D.edgeFromLift x y h, Prod.ext
      ((D.edgeFromLift_tail h).trans hx) ((D.edgeFromLift_head h).trans hy)⟩

theorem mem_pairGraph_strict_iff_lifts (D : Diagram n) (u v : Fin n) :
    (u, v) ∈ D.pairGraph.strictEdges ↔
      ∃ x y : ℤ, D.residue x = u ∧ D.residue y = v ∧ D.liftStep ∅ x y := by
  rw [D.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨e, he, heq⟩
    obtain ⟨hu, hv⟩ := Prod.mk.inj heq
    have hx := Orientation.residue_intCast_eq (D := D) e.tail
    have hy := D.residue_add_length e (e.tail.val : ℤ) hx
    exact ⟨e.tail.val, (e.tail.val : ℤ) + e.length.val, hx.trans hu, hy.trans hv,
      e, Finset.mem_union_left _ he, hx, rfl⟩
  · rintro ⟨x, y, hx, hy, e, he, ht, hlen⟩
    have hhead : D.residue y = e.head := by rw [hlen]; exact D.residue_add_length e x ht
    exact ⟨e, by simpa using he, Prod.ext (ht.symm.trans hx) (hhead.symm.trans hy)⟩

namespace InteriorMergedComponent

variable {r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

/-- The finite strict graph is conjugate under column reversal. -/
theorem strictPairs_reversal_iff (u v : Fin n) :
    (K.reversalPerm u, K.reversalPerm v) ∈ K.reversalTarget.pairGraph.strictEdges ↔
      (u, v) ∈ D.pairGraph.strictEdges := by
  rw [mem_pairGraph_strict_iff_lifts, mem_pairGraph_strict_iff_lifts]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    obtain ⟨x, rfl⟩ := K.reversalLift.surjective x
    obtain ⟨y, rfl⟩ := K.reversalLift.surjective y
    rw [K.reversalLift_residue] at hx hy
    exact ⟨x, y, K.reversalPerm.injective hx, K.reversalPerm.injective hy,
      (K.liftStep_empty_reversal_iff x y).mp h⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨K.reversalLift x, K.reversalLift y,
      (K.reversalLift_residue x).trans (congrArg K.reversalPerm hx),
      (K.reversalLift_residue y).trans (congrArg K.reversalPerm hy),
      (K.liftStep_empty_reversal_iff x y).mpr h⟩

/-- All actual natural edges with an exterior endpoint are transported. -/
theorem naturalPairs_reversal_iff (u v : Fin n)
    (houtside : u ∉ K.componentVertices ∨ v ∉ K.componentVertices) :
    (K.reversalPerm u, K.reversalPerm v) ∈ K.reversalTarget.naturalPairs ↔
      (u, v) ∈ D.naturalPairs := by
  rw [mem_naturalPairs_iff_lifts, mem_naturalPairs_iff_lifts]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    obtain ⟨x, rfl⟩ := K.reversalLift.surjective x
    obtain ⟨y, rfl⟩ := K.reversalLift.surjective y
    rw [K.reversalLift_residue] at hx hy
    have hx' := K.reversalPerm.injective hx
    have hy' := K.reversalPerm.injective hy
    refine ⟨x, y, hx', hy', (K.boundaryNaturalLift_reversal_iff x y ?_).mp h⟩
    simpa only [hx', hy'] using houtside
  · rintro ⟨x, y, hx, hy, h⟩
    refine ⟨K.reversalLift x, K.reversalLift y,
      (K.reversalLift_residue x).trans (congrArg K.reversalPerm hx),
      (K.reversalLift_residue y).trans (congrArg K.reversalPerm hy),
      (K.boundaryNaturalLift_reversal_iff x y ?_).mpr h⟩
    simpa only [hx, hy] using houtside

/-- All actual normal edges with an exterior endpoint are transported. -/
theorem normalPairs_reversal_iff (u v : Fin n)
    (houtside : u ∉ K.componentVertices ∨ v ∉ K.componentVertices) :
    (K.reversalPerm u, K.reversalPerm v) ∈ K.reversalTarget.pairGraph.normalEdges ↔
      (u, v) ∈ D.pairGraph.normalEdges := by
  rw [normalPairs_eq_sdiff, normalPairs_eq_sdiff]
  simp only [Finset.mem_sdiff, K.naturalPairs_reversal_iff u v houtside,
    K.strictPairs_reversal_iff u v]

end InteriorMergedComponent
end VerticalStripLLT.Circular.Diagram

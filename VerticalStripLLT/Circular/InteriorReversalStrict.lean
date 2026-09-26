import VerticalStripLLT.Circular.InteriorReversalLift
import VerticalStripLLT.Circular.InteriorReversalHeads

/-! Strict edges of the actual smaller target, including their positive integer lifts. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

/-- A strict lift is determined by its strict head and that head's boundary. -/
theorem liftStep_empty_iff_strictAt_boundary (D : Diagram n) (x y : ℤ) :
    D.liftStep ∅ x y ↔ D.strictAt y ∧ D.boundary y = x := by
  constructor
  · rintro ⟨e, he, hx, hy⟩
    have he' : e ∈ D.strict := by simpa using he
    have hh : D.residue y = e.head := by rw [hy]; exact D.residue_add_length e x hx
    refine ⟨⟨e, he', hh.symm⟩, ?_⟩
    rw [boundary, hh, ← (D.strict_corner e he').1, hy]
    ring
  · rintro ⟨⟨e, he, hh⟩, hb⟩
    have hlen : (e.length.val : ℤ) = y - x := by
      rw [boundary, ← hh, ← (D.strict_corner e he).1] at hb
      lia
    have hl := D.naturalLift_of_head_length hh hlen
    exact ⟨e, Finset.mem_union_left _ he, hl.1, hl.2⟩

namespace InteriorMergedComponent

variable {r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

theorem reversalTarget_heads :
    K.reversalTarget.strict.image Edge.head = K.reversalHeads := by
  exact Diagram.fromHeads_strict_head_image _ _ _

/-- Strict rows are transported by the periodic reversal. -/
theorem strictAt_reversalLift_iff (z : ℤ) :
    K.reversalTarget.strictAt (K.reversalLift z) ↔ D.strictAt z := by
  simp only [strictAt, ← Finset.mem_image]
  rw [K.reversalTarget_heads, K.reversalLift_residue, K.reversalHeads_mem_iff,
    K.reversalPerm_involutive]

/-- At each original strict row the new boundary is the lifted old boundary. -/
theorem boundary_reversalLift_of_strictAt (z : ℤ) (hz : D.strictAt z) :
    K.reversalTarget.boundary (K.reversalLift z) = K.reversalLift (D.boundary z) := by
  have hs := D.selected_of_strictAt hz
  by_cases hc : D.residue z ∈ K.componentVertices
  · obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hc
    rw [← ha, K.selected_to_vertex_iff a.isLt] at hs
    obtain ⟨hap, hpred⟩ := hs
    have harea := K.reversalArea_reversed_length a hap
    rw [boundary, K.reversalLift_residue, ← ha]
    change K.reversalLift z - (K.reversalArea.area (K.reversalPerm (K.vertex a.val)) : ℤ) = _
    rw [harea]
    change z + K.reversalShift (D.residue z) -
      ((D.area.area (K.vertex a.val) : ℤ) + columnDisplacement (r + j) j a.val -
        columnDisplacement (r + j) j (a.val - 1)) =
      D.boundary z + K.reversalShift (D.residue (D.boundary z))
    rw [← ha, K.reversalShift_vertex a, hpred,
      K.reversalShift_vertex ⟨a.val - 1, by have := a.isLt; lia⟩, boundary, ← ha]
    ring
  · have hp : D.residue (D.boundary z) ∉ K.componentVertices := by
      intro hp
      exact hc (K.selected_from_component _ _ hp hs)
    have hzfix : K.reversalLift z = z := by
      change z + K.reversalShift (D.residue z) = z
      rw [K.reversalShift_of_not_mem _ hc, add_zero]
    have hbfix : K.reversalLift (D.boundary z) = D.boundary z := by
      change D.boundary z + K.reversalShift (D.residue (D.boundary z)) = D.boundary z
      rw [K.reversalShift_of_not_mem _ hp, add_zero]
    rw [hzfix, hbfix]
    change z - ((D.area.area (D.residue z) - K.reversalDecrement (D.residue z) : ℕ) : ℤ) =
      z - (D.area.area (D.residue z) : ℤ)
    rw [K.reversalDecrement_of_not_mem _ hc, Nat.sub_zero]

/-- The actual strict lifted graphs are conjugate, with no period ambiguity. -/
theorem liftStep_empty_reversal_iff (x y : ℤ) :
    K.reversalTarget.liftStep ∅ (K.reversalLift x) (K.reversalLift y) ↔
      D.liftStep ∅ x y := by
  rw [liftStep_empty_iff_strictAt_boundary, liftStep_empty_iff_strictAt_boundary,
    K.strictAt_reversalLift_iff]
  constructor
  · rintro ⟨hy, hb⟩
    rw [K.boundary_reversalLift_of_strictAt y hy] at hb
    exact ⟨hy, K.reversalLift.injective hb⟩
  · rintro ⟨hy, hb⟩
    exact ⟨hy, (K.boundary_reversalLift_of_strictAt y hy).trans (congrArg K.reversalLift hb)⟩

end InteriorMergedComponent
end VerticalStripLLT.Circular.Diagram

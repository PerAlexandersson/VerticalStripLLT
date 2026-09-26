import VerticalStripLLT.Circular.InteriorBoundaryAvoidance
import VerticalStripLLT.Circular.InteriorReversalSource

/-! Exterior boundary intervals are preserved by the actual smaller target. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

/-- An exterior head's boundary cannot cut the interior of any lifted column. -/
theorem boundary_not_inside_column (a : Fin (r + j)) (x : ℤ)
    (hx : D.residue x = K.vertex a.val) (z : ℤ)
    (hz : D.residue z ∉ K.componentVertices) :
    ¬ (x - ((a.val / j : ℕ) : ℤ) < D.boundary z ∧
      D.boundary z ≤ x + (colLen (r + j) j (a.val % j) : ℤ) - 1 -
        ((a.val / j : ℕ) : ℤ)) := by
  rintro ⟨hlo, hhi⟩
  have hj : 0 < j := by have := K.two_le; lia
  let h' := (D.boundary z - x + ((a.val / j : ℕ) : ℤ)).toNat
  have hcast : (h' : ℤ) = D.boundary z - x + ((a.val / j : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (by lia)
  have hp : 0 < h' := by lia
  have hrow : h' < colLen (r + j) j (a.val % j) := by lia
  have hi : a.val % j + j * h' < r + j :=
    (lt_colLen_iff hj ((Nat.mod_le _ _).trans_lt a.isLt)).mp hrow
  have hloindex : j ≤ a.val % j + j * h' := by
    have hm := Nat.mul_le_mul_left j (show 1 ≤ h' by lia)
    simpa using hm.trans (Nat.le_add_left (j * h') (a.val % j))
  have hs := K.residue_column_shift (a.val % j) (a.val / j) h' (Nat.mod_lt _ hj)
    (by rw [Nat.mod_add_div]; exact a.isLt) hi x (by rwa [Nat.mod_add_div])
  have heq : x + (h' : ℤ) - ((a.val / j : ℕ) : ℤ) = D.boundary z := by lia
  rw [heq] at hs
  exact K.boundary_avoids_column_interior z hz ⟨a.val % j + j * h', hi⟩ hloindex hs

/-- Reversal leaves membership above an exterior head's incoming threshold unchanged. -/
theorem outside_boundary_le_reversalLift_iff (x z : ℤ)
    (hz : D.residue z ∉ K.componentVertices) :
    D.boundary z ≤ K.reversalLift x ↔ D.boundary z ≤ x := by
  by_cases hx : D.residue x ∈ K.componentVertices
  · obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hx
    have hb := K.reversalLift_interval a x ha.symm
    have hn := K.boundary_not_inside_column a x ha.symm z hz
    dsimp only at hb
    lia
  · rw [K.reversalLift_eq_self_of_not_mem x hx]

/-- Every exterior head keeps exactly its original boundary. -/
theorem reversalTarget_boundary_outside (z : ℤ)
    (hz : D.residue z ∉ K.componentVertices) :
    K.reversalTarget.boundary z = D.boundary z := by
  change z - ((D.area.area (D.residue z) - K.reversalDecrement (D.residue z) : ℕ) : ℤ) =
    z - (D.area.area (D.residue z) : ℤ)
  rw [K.reversalDecrement_of_not_mem _ hz, Nat.sub_zero]

/-- The only nonstrict row in the merged component is its original source. -/
theorem residue_eq_source_of_not_strictAt (z : ℤ)
    (hz : D.residue z ∈ K.componentVertices) (hn : ¬ D.strictAt z) :
    D.residue z = K.vertex 0 := by
  obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hz
  have ha0 : a.val = 0 := by
    by_contra ha0
    exact hn (K.strictAt_of_residue_vertex a (by lia) z ha.symm)
  rw [← ha, ha0]

/-- Every natural edge with an exterior endpoint has exactly its transported integer lift. -/
theorem boundaryNaturalLift_reversal_iff (x y : ℤ)
    (houtside : D.residue x ∉ K.componentVertices ∨ D.residue y ∉ K.componentVertices) :
    K.reversalTarget.boundaryNaturalLift (K.reversalLift x) (K.reversalLift y) ↔
      D.boundaryNaturalLift x y := by
  by_cases hy : D.residue y ∉ K.componentVertices
  · rw [K.reversalLift_eq_self_of_not_mem y hy]
    change (K.reversalTarget.boundary y ≤ K.reversalLift x ∧ K.reversalLift x < y) ↔ _
    rw [K.reversalTarget_boundary_outside y hy, K.outside_boundary_le_reversalLift_iff x y hy,
      K.reversalLift_lt_outside_iff x y hy]
    rfl
  · have hx : D.residue x ∉ K.componentVertices := houtside.resolve_right hy
    rw [K.reversalLift_eq_self_of_not_mem x hx]
    change (K.reversalTarget.boundary (K.reversalLift y) ≤ x ∧ x < K.reversalLift y) ↔ _
    rw [K.outside_lt_reversalLift_iff y x hx]
    by_cases hs : D.strictAt y
    · rw [K.boundary_reversalLift_of_strictAt y hs, K.reversalLift_le_outside_iff _ x hx]
      rfl
    · have hsource := K.residue_eq_source_of_not_strictAt y (by simpa using hy) hs
      rw [K.boundary_source_le_outside_iff y x hsource hx]
      rfl

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

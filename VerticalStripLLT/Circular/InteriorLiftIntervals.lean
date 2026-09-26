import VerticalStripLLT.Circular.InteriorReversalStrict

/-! Order facts for the periodic lift of an interior column reversal. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- The lifted reversal fixes every row whose residue is outside the isolated
component. -/
theorem reversalLift_eq_self_of_not_mem (z : ℤ)
    (hz : D.residue z ∉ K.componentVertices) : K.reversalLift z = z := by
  change z + K.reversalShift (D.residue z) = z
  rw [K.reversalShift_of_not_mem _ hz]
  ring

/-- Every integer position between the ends of a lifted column belongs to the component. -/
theorem residue_mem_column_interval (a : Fin (r + j)) (x : ℤ)
    (hx : D.residue x = K.vertex a.val) (z : ℤ)
    (hlo : x - ((a.val / j : ℕ) : ℤ) ≤ z)
    (hhi : z ≤ x + (colLen (r + j) j (a.val % j) : ℤ) - 1 - ((a.val / j : ℕ) : ℤ)) :
    D.residue z ∈ K.componentVertices := by
  have hj : 0 < j := by have := K.two_le; lia
  let h' := (z - x + ((a.val / j : ℕ) : ℤ)).toNat
  have hcast : (h' : ℤ) = z - x + ((a.val / j : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (by lia)
  have hrow : h' < colLen (r + j) j (a.val % j) := by lia
  have hi : a.val % j + j * h' < r + j :=
    (lt_colLen_iff hj ((Nat.mod_le _ _).trans_lt a.isLt)).mp hrow
  have hs := K.residue_column_shift (a.val % j) (a.val / j) h' (Nat.mod_lt _ hj)
    (by rw [Nat.mod_add_div]; exact a.isLt) hi x (by rwa [Nat.mod_add_div])
  have heq : x + (h' : ℤ) - ((a.val / j : ℕ) : ℤ) = z := by lia
  rw [heq] at hs
  exact (K.mem_componentVertices_iff _).mpr ⟨⟨a.val % j + j * h', hi⟩, hs.symm⟩

/-- A component point and its reflected point stay inside the same lifted column. -/
theorem reversalLift_interval (a : Fin (r + j)) (x : ℤ)
    (hx : D.residue x = K.vertex a.val) :
    let lo := x - ((a.val / j : ℕ) : ℤ)
    let hi := x + (colLen (r + j) j (a.val % j) : ℤ) - 1 - ((a.val / j : ℕ) : ℤ)
    lo ≤ x ∧ x ≤ hi ∧ lo ≤ K.reversalLift x ∧ K.reversalLift x ≤ hi := by
  have hj : 0 < j := by have := K.two_le; lia
  have hrow : a.val / j < colLen (r + j) j (a.val % j) :=
    (lt_colLen_iff hj ((Nat.mod_le _ _).trans_lt a.isLt)).mpr
      (by rw [Nat.mod_add_div]; exact a.isLt)
  have hs : K.reversalLift x = x + columnDisplacement (r + j) j a.val := by
    change x + K.reversalShift (D.residue x) = _
    rw [hx, K.reversalShift_vertex a]
  rw [hs]
  dsimp only [columnDisplacement]
  have hrowInt : ((a.val / j : ℕ) : ℤ) < (colLen (r + j) j (a.val % j) : ℤ) := by
    exact_mod_cast hrow
  have hnonneg := Int.natCast_nonneg (a.val / j)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Reversal preserves both comparisons against any point outside the component. -/
theorem reversalLift_compare_outside (x y : ℤ)
    (hy : D.residue y ∉ K.componentVertices) :
    (K.reversalLift x < y ↔ x < y) ∧ (y < K.reversalLift x ↔ y < x) := by
  by_cases hx : D.residue x ∈ K.componentVertices
  · obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hx
    have hb := K.reversalLift_interval a x ha.symm
    have hn := fun hlo hhi => hy (K.residue_mem_column_interval a x ha.symm y hlo hhi)
    dsimp only at hb
    lia
  · rw [K.reversalLift_eq_self_of_not_mem x hx]
    exact ⟨Iff.rfl, Iff.rfl⟩

theorem reversalLift_lt_outside_iff (x y : ℤ)
    (hy : D.residue y ∉ K.componentVertices) : K.reversalLift x < y ↔ x < y :=
  (K.reversalLift_compare_outside x y hy).1

theorem outside_lt_reversalLift_iff (x y : ℤ)
    (hy : D.residue y ∉ K.componentVertices) : y < K.reversalLift x ↔ y < x :=
  (K.reversalLift_compare_outside x y hy).2

theorem reversalLift_le_outside_iff (x y : ℤ)
    (hy : D.residue y ∉ K.componentVertices) : K.reversalLift x ≤ y ↔ x ≤ y := by
  simpa only [not_lt] using not_congr (K.outside_lt_reversalLift_iff x y hy)

theorem outside_le_reversalLift_iff (x y : ℤ)
    (hy : D.residue y ∉ K.componentVertices) : y ≤ K.reversalLift x ↔ y ≤ x := by
  simpa only [not_lt] using not_congr (K.reversalLift_lt_outside_iff x y hy)

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

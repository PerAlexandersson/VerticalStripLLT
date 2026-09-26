import VerticalStripLLT.Circular.InteriorLiftIntervals

/-! Reversal preserves the order of integer sinks. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

private theorem component_residue_of_sink (A : Finset (Edge D.area)) (x : ℤ)
    (hx : ∀ z, ¬ D.liftStep A x z)
    (hxc : D.residue x ∈ K.componentVertices) :
    D.residue x = K.vertex (r + j - 1) := by
  obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hxc
  by_contra hlast
  have ha' : a.val + 1 < r + j := by
    have : a.val ≠ r + j - 1 := by
      intro h
      apply hlast
      rw [← ha, h]
    have := a.isLt
    lia
  obtain ⟨e, he, htail, hhead⟩ := K.exists_strict_edge (a.val + 1)
    (by lia) ha'
  simp only [Nat.add_sub_cancel] at htail
  have hres : D.residue x = e.tail := ha.symm.trans htail.symm
  have hs : D.liftStep A x (x + (e.length.val : ℤ)) := by
    refine ⟨e, Finset.mem_union_left _ he, hres, rfl⟩
  exact (hx _ hs).elim

theorem reversalLift_order_sinks (A : Finset (Edge D.area)) (x y : ℤ)
    (hx : ∀ z, ¬ D.liftStep A x z) (hy : ∀ z, ¬ D.liftStep A y z)
    (hxy : x ≤ y) : K.reversalLift x ≤ K.reversalLift y := by
  by_cases hxc : D.residue x ∈ K.componentVertices
  · have hxs := K.component_residue_of_sink A x hx hxc
    by_cases hyc : D.residue y ∈ K.componentVertices
    · have hys := K.component_residue_of_sink A y hy hyc
      have hres : D.residue x = D.residue y := hxs.trans hys.symm
      change x + K.reversalShift (D.residue x) ≤
        y + K.reversalShift (D.residue y)
      rw [hres]
      lia
    · rw [K.reversalLift_eq_self_of_not_mem y hyc]
      exact (K.reversalLift_le_outside_iff x y hyc).mpr hxy
  · rw [K.reversalLift_eq_self_of_not_mem x hxc]
    exact (K.outside_le_reversalLift_iff y x hxc).mpr hxy

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

import VerticalStripLLT.Circular.InteriorReversalStrict
import VerticalStripLLT.Circular.ContactEndpoints
import VerticalStripLLT.Circular.HRVPotential

/-! A boundary value is pinned by two adjacent strict rows. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem eq_of_boundary_eq_of_adjacent_strict (D : Diagram n) {z v : ℤ}
    (hprev : D.strictAt (v - 1)) (hv : D.strictAt v)
    (hb : D.boundary z = D.boundary v) : z = v := by
  have hleft := D.strictAt_boundary_lt hprev
  have hright := D.strictAt_boundary_lt hv
  simp only [sub_add_cancel] at hleft
  by_cases hz : z < v
  · have hz' : z ≤ v - 1 := by lia
    have hm := D.boundary_monotone (show z ≤ v - 1 by exact hz')
    have : D.boundary z < D.boundary v := lt_of_le_of_lt hm hleft
    lia
  · by_cases hz' : v < z
    · have hz'' : v + 1 ≤ z := by lia
      have hm := D.boundary_monotone hz''
      have : D.boundary v < D.boundary z := lt_of_lt_of_le hright hm
      lia
    · lia

namespace InteriorMergedComponent

variable {r j : ℕ} {D : Diagram n} {t : ℤ} (K : InteriorMergedComponent D t r j)

/-- Every noninitial chain vertex is an actual strict row on every integer lift. -/
theorem strictAt_of_residue_vertex (a : Fin (r + j)) (ha : 0 < a.val)
    (z : ℤ) (hz : D.residue z = K.vertex a.val) : D.strictAt z := by
  obtain ⟨e, he, _, hh⟩ := K.exists_strict_edge a.val ha a.isLt
  exact ⟨e, he, hh.trans hz.symm⟩

/-- An outside head's boundary never lies in the interior of a moved column. -/
theorem boundary_avoids_column_interior (z : ℤ)
    (hz : D.residue z ∉ K.componentVertices) (a : Fin (r + j)) (ha : j ≤ a.val) :
    D.residue (D.boundary z) ≠ K.vertex a.val := by
  intro hbound
  have hj := K.two_le
  have hjr := K.jump_lt
  by_cases hlast : a.val = r + j - 1
  · rw [hlast, K.sink] at hbound
    obtain ⟨k, hk⟩ := D.residue_eq_exists_period hbound
    exact K.root_eligible.boundary_avoids D z k hk
  have hanext : a.val + 1 < r + j := by have := a.isLt; lia
  obtain ⟨e, he, ht, hh⟩ := K.exists_strict_edge (a.val + 1) (by lia) hanext
  simp only [Nat.add_sub_cancel] at ht
  let v : ℤ := D.boundary z + (e.length.val : ℤ)
  have hvres : D.residue v = K.vertex (a.val + 1) :=
    (D.residue_add_length e (D.boundary z) (hbound.trans ht.symm)).trans hh
  have hv : D.strictAt v := ⟨e, he, hh.trans hvres.symm⟩
  have hvbound : D.boundary v = D.boundary z := by
    rw [boundary, hvres, ← hh, ← (D.strict_corner e he).1]
    dsimp [v]
    ring
  have hprevindex : a.val + 1 - j < r := by lia
  have hprevres : D.residue (v - 1) = K.vertex (a.val + 1 - j) := by
    apply D.area.next_injective
    rw [K.next_jump _ hprevindex, Nat.sub_add_cancel (by lia : j ≤ a.val + 1),
      ← D.residue_succ, sub_add_cancel, hvres]
  have hprev := K.strictAt_of_residue_vertex
    ⟨a.val + 1 - j, by lia⟩ (by lia) (v - 1) hprevres
  have hzeq := D.eq_of_boundary_eq_of_adjacent_strict hprev hv hvbound.symm
  apply hz
  rw [hzeq, hvres]
  exact (K.mem_componentVertices_iff _).mpr ⟨⟨a.val + 1, hanext⟩, rfl⟩

end InteriorMergedComponent
end VerticalStripLLT.Circular.Diagram

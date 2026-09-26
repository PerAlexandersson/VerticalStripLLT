import VerticalStripLLT.Circular.HRVPotential

/-! A zero-area cut confines every lifted selected walk to one period. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem boundary_eq_self_of_area_zero {c : ℤ}
    (hc : D.area.area (D.residue c) = 0) : D.boundary c = c := by
  simp [boundary, hc]

theorem liftStep_interval {A : Finset (Edge D.area)} {c z w : ℤ}
    (hc : D.area.area (D.residue c) = 0)
    (hz : c ≤ z ∧ z < c + n) (h : D.liftStep A z w) :
    c ≤ w ∧ w < c + n := by
  rcases h with ⟨e, _, htail, hw⟩
  have hpos := e.length_pos
  have hzw : z < w := by
    have : (0 : ℤ) < e.length.val := by exact_mod_cast hpos
    lia
  have hhead : e.head = D.residue w := by
    rw [hw]
    exact (D.residue_add_length e z htail).symm
  have hlen : (e.length.val : ℤ) = w - z := by rw [hw]; ring
  have hbound := (D.boundaryNaturalLift_of_edge hhead hlen).1
  have hbc := D.boundary_eq_self_of_area_zero hc
  have hbcn : D.boundary (c + n) = c + n := by
    rw [show c + n = c + (n : ℤ) * 1 by ring, D.boundary_add_period, hbc]
  constructor
  · linarith
  · by_contra hn
    have hcw : c + n ≤ w := le_of_not_gt hn
    have hmono := D.boundary_monotone hcw
    rw [hbcn] at hmono
    linarith

theorem reflTransGen_interval {A : Finset (Edge D.area)} {c z w : ℤ}
    (hc : D.area.area (D.residue c) = 0)
    (hz : c ≤ z ∧ z < c + n)
    (h : Relation.ReflTransGen (D.liftStep A) z w) : c ≤ w ∧ w < c + n := by
  induction h with
  | refl => exact hz
  | tail _ hstep ih => exact D.liftStep_interval hc ih hstep

end Diagram

namespace Orientation

/-- At a zero-area cut the circular maximum is attained within the same period. -/
theorem liftedHRV_interval {n : ℕ} {D : Diagram n} (θ : Orientation D) {c z : ℤ}
    (hc : D.area.area (D.residue c) = 0) (hz : c ≤ z ∧ z < c + n) :
    c ≤ θ.liftedHRV z ∧ θ.liftedHRV z < c + n := by
  exact D.reflTransGen_interval hc hz (θ.liftedHRV_reachable z)

end Orientation
end VerticalStripLLT.Circular

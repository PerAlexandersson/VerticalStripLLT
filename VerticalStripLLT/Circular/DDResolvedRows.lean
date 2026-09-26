import VerticalStripLLT.Circular.DDLocalData

/-! Row and boundary formulas for the concrete DD successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem DDLocalData.resolved_area :
    B.resolved.area.area = Function.update
      (Function.update D.area.area
        (D.residue (D.boundary t + 1))
        (D.area.area (D.residue (D.boundary t)) + 1))
      (D.residue t) (D.area.area (D.residue t) - 1) := by
  unfold resolved ddResolved
  rw [dnSuccessor_area]
  change Function.update
    (Function.update D.area.area (D.area.next B.e.head) (D.area.area B.e.head + 1))
    B.f.head (D.area.area B.f.head - 1) = _
  have hnext : D.area.next B.e.head = D.residue (D.boundary t + 1) :=
    B.head.symm.trans B.gh
  rw [hnext, B.eh, B.fh]

theorem DDLocalData.resolved_residue (z : ℤ) :
    B.resolved.residue z = D.residue z := rfl

theorem DDLocalData.resolved_boundary_of_ne (z : ℤ)
    (h₁ : D.residue z ≠ D.residue (D.boundary t + 1))
    (h₂ : D.residue z ≠ D.residue t) :
    B.resolved.boundary z = D.boundary z := by
  rw [boundary, boundary, B.resolved_residue, B.resolved_area]
  rw [Function.update_of_ne h₂, Function.update_of_ne h₁]

theorem DDLocalData.resolved_boundary_rows :
    B.resolved.boundary (D.boundary t + 1) = D.boundary (D.boundary t) ∧
      B.resolved.boundary (D.boundary t) = D.boundary (D.boundary t) := by
  have hn : 2 ≤ n := by
    have hp := B.e.length_pos
    have hc := (D.strict_corner B.e B.he).1
    have hb := B.areaBound
    lia
  have hroot : 2 ≤ D.area.area (D.residue t) := by
    rw [← B.fh, ← (D.strict_corner B.f B.hf).1]
    exact B.rootLength
  have hbound := D.area.bound (D.residue t)
  have hct : D.residue (D.boundary t + 1) ≠ D.residue t := by
    intro hh
    have heq := D.eq_of_residue_eq_of_bounds hh.symm (by unfold boundary; lia)
      (by unfold boundary; lia)
    unfold boundary at heq
    lia
  constructor
  · rw [boundary, B.resolved_residue, B.resolved_area]
    simp only [Function.update_of_ne hct, Function.update_self]
    simp only [Nat.cast_add, Nat.cast_one, boundary]
    ring
  · have h₁ : D.residue (D.boundary t) ≠ D.residue (D.boundary t + 1) := by
      exact D.residue_p_ne_succ hn _
    have h₂ : D.residue (D.boundary t) ≠ D.residue t := by
      intro hh
      have heq := D.eq_of_residue_eq_of_bounds hh.symm (by unfold boundary; lia)
        (by unfold boundary; lia)
      unfold boundary at heq
      lia
    exact B.resolved_boundary_of_ne _ h₁ h₂

end VerticalStripLLT.Circular.Diagram

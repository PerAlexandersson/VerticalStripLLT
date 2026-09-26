import VerticalStripLLT.Circular.LiftStep
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-! Integer boundary functions for periodic circular area data. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The lifted left boundary of the row ending at the integer position `z`. -/
def boundary (z : ℤ) : ℤ :=
  z - (D.area.area (D.residue z) : ℤ)

theorem residue_succ (z : ℤ) : D.residue (z + 1) = D.area.next (D.residue z) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  change (z + 1) % (n : ℤ) = (((D.residue z).val + 1) % n : ℕ)
  simp only [Int.natCast_mod, Nat.cast_add, Nat.cast_one, D.residue_coe_val,
    Int.add_emod, Int.emod_emod]

theorem boundary_step_le (z : ℤ) : D.boundary z ≤ D.boundary (z + 1) := by
  rw [boundary, boundary, D.residue_succ]
  have hc := D.area.cyclic (D.residue z)
  have hc' :
      (D.area.area (D.area.next (D.residue z)) : ℤ) ≤
        (D.area.area (D.residue z) : ℤ) + 1 := by
    exact_mod_cast hc
  lia

theorem boundary_monotone : Monotone D.boundary := by
  apply monotone_int_of_le_succ
  intro z
  simpa [add_comm] using D.boundary_step_le z

theorem boundary_add_period (z k : ℤ) :
    D.boundary (z + (n : ℤ) * k) = D.boundary z + (n : ℤ) * k := by
  rw [boundary, boundary, D.residue_add_period]
  lia

theorem boundary_le_self (z : ℤ) : D.boundary z ≤ z := by
  rw [boundary]
  exact sub_le_self _ (by positivity)

theorem self_sub_period_lt_boundary (z : ℤ) :
    z - (n : ℤ) < D.boundary z := by
  rw [boundary]
  have ha : D.area.area (D.residue z) < n := D.area.bound _
  have ha' : (D.area.area (D.residue z) : ℤ) < (n : ℤ) := by
    exact_mod_cast ha
  lia

theorem no_boundary_gap (z p : ℤ)
    (hp : D.boundary z = p)
    (hgap : p + 2 ≤ D.boundary (z + 1)) :
    ∀ w : ℤ, D.boundary w ≠ p + 1 := by
  intro w
  by_cases hw : w ≤ z
  · intro hrow
    have hle := D.boundary_monotone hw
    rw [hp] at hle
    rw [hrow] at hle
    lia
  · have hw' : z + 1 ≤ w := by lia
    have hle := D.boundary_monotone hw'
    intro hrow
    rw [hrow] at hle
    lia

end Diagram
end VerticalStripLLT.Circular

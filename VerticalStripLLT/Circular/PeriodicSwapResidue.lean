import VerticalStripLLT.Circular.PeriodicSwap
import VerticalStripLLT.Circular.LiftedBoundary
import VerticalStripLLT.Circular.HRVRoots
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The action of a periodic integer swap on circular residues. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem residue_eq_iff_mod_sub_zero {x y : ℤ} :
    D.residue x = D.residue y ↔ (x - y) % n = 0 := by
  constructor
  · intro hxy
    have hval := congrArg (fun a : Fin n => (a.val : ℤ)) hxy
    rw [D.residue_coe_val, D.residue_coe_val] at hval
    rw [Int.sub_emod, hval, sub_self, Int.zero_emod]
  · intro hmod
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x = y + (n : ℤ) * k := by
      refine ⟨(x - y) / n, ?_⟩
      have hdiv := Int.mul_ediv_add_emod (x - y) n
      rw [hmod] at hdiv
      linarith
    rw [hk, D.residue_add_period]

theorem residue_p_ne_succ (hn : 2 ≤ n) (p : ℤ) :
    D.residue p ≠ D.residue (p + 1) := by
  intro h
  have hmod : (p + 1 - p) % n = 0 :=
    (D.residue_eq_iff_mod_sub_zero).mp h.symm
  have hone : (1 : ℤ) % n = 1 :=
    Int.emod_eq_of_lt (by lia)
      (by exact_mod_cast (Nat.lt_of_succ_le hn))
  rw [show p + 1 - p = 1 by ring, hone] at hmod
  norm_num at hmod

private theorem eq_add_period_of_emod_zero {p z : ℤ}
    (h : (z - p) % n = 0) :
    ∃ k : ℤ, z = p + (n : ℤ) * k := by
  refine ⟨(z - p) / n, ?_⟩
  have hdiv := Int.mul_ediv_add_emod (z - p) n
  rw [h] at hdiv
  linarith

private theorem eq_succ_add_period_of_emod_one {p z : ℤ}
    (h : (z - p) % n = 1) :
    ∃ k : ℤ, z = p + 1 + (n : ℤ) * k := by
  refine ⟨(z - p) / n, ?_⟩
  have hdiv := Int.mul_ediv_add_emod (z - p) n
  rw [h] at hdiv
  linarith

theorem residue_periodicSwap (hn : 2 ≤ n) (p z : ℤ) :
    D.residue (periodicSwap n p z) =
      Equiv.swap (D.residue p) (D.residue (p + 1)) (D.residue z) := by
  have hne := D.residue_p_ne_succ hn p
  unfold periodicSwap
  by_cases hzero : (z - p) % n = 0
  · have hres : D.residue z = D.residue p :=
      (D.residue_eq_iff_mod_sub_zero).mpr hzero
    rw [ite_eq_left hzero]
    calc
      D.residue (z + 1) = D.area.next (D.residue z) := D.residue_succ z
      _ = D.area.next (D.residue p) := by rw [hres]
      _ = D.residue (p + 1) := (D.residue_succ p).symm
      _ = Equiv.swap (D.residue p) (D.residue (p + 1)) (D.residue z) := by
        rw [hres, Equiv.swap_apply_left]
  · by_cases hone : (z - p) % n = 1
    · obtain ⟨k, hk⟩ := eq_succ_add_period_of_emod_one (n := n) hone
      have hres : D.residue z = D.residue (p + 1) := by
        rw [hk, D.residue_add_period]
      have hminus : D.residue (z - 1) = D.residue p := by
        calc
          D.residue (z - 1) = D.residue (p + (n : ℤ) * k) := by
            rw [hk]
            exact congrArg D.residue (by ring)
          _ = D.residue p := D.residue_add_period p k
      rw [ite_eq_right hzero, ite_eq_left hone]
      calc
        D.residue (z - 1) = D.residue p := hminus
        _ = Equiv.swap (D.residue p) (D.residue (p + 1))
            (D.residue (p + 1)) := by rw [Equiv.swap_apply_right]
        _ = Equiv.swap (D.residue p) (D.residue (p + 1)) (D.residue z) := by
          rw [hres]
    · have hnep : D.residue z ≠ D.residue p := by
        intro hres
        exact hzero ((D.residue_eq_iff_mod_sub_zero).mp hres)
      have hneps : D.residue z ≠ D.residue (p + 1) := by
        intro hres
        have hmod := (D.residue_eq_iff_mod_sub_zero).mp hres
        have hdiv := Int.mul_ediv_add_emod (z - (p + 1)) (n : ℤ)
        have hz : z - p = (n : ℤ) * ((z - (p + 1)) / n) + 1 := by lia
        have h1 : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by exact_mod_cast hn)
        apply hone
        rw [hz, Int.add_emod]
        simp [h1]
      rw [ite_eq_right hzero, ite_eq_right hone]
      exact (Equiv.swap_apply_of_ne_of_ne hnep hneps).symm

end Diagram
end VerticalStripLLT.Circular

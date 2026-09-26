import VerticalStripLLT.ElementaryColorings
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite coloring sums for an inserted vertex and an isolated vertex. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

theorem inserted_strictMono_sum (L m : ℕ) (j : Fin (L + 1)) :
    (∑ z : Fin m, ∑ c : Fin L → Fin m,
      if StrictMono (j.insertNth z c) then
        MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) =
      MvPolynomial.esymm (Fin m) Q (L + 1) := by
  let E : (Fin m × (Fin L → Fin m)) ≃ (Fin (L + 1) → Fin m) :=
    Fin.insertNthEquiv (fun _ : Fin (L + 1) => Fin m) j
  calc
    (∑ z : Fin m, ∑ c : Fin L → Fin m,
        if StrictMono (j.insertNth z c) then
          MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) =
        ∑ p : Fin m × (Fin L → Fin m),
          if StrictMono (j.insertNth p.1 p.2) then
            MvPolynomial.X p.1 * ∏ i, MvPolynomial.X (p.2 i) else 0 :=
      by rw [Fintype.sum_prod_type]
    _ = ∑ d : Fin (L + 1) → Fin m,
          if StrictMono d then ∏ i, MvPolynomial.X (d i) else 0 := by
      refine Fintype.sum_equiv E _ _ ?_
      intro p
      have hp : (∏ i,
          MvPolynomial.X ((j.insertNth (α := fun _ => Fin m) p.1 p.2) i) : XPoly m) =
          MvPolynomial.X p.1 * ∏ i, MvPolynomial.X (p.2 i) := by
        rw [Fin.prod_univ_succAbove _ j]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      change _ = if StrictMono (j.insertNth (α := fun _ => Fin m) p.1 p.2) then
        (∏ i, MvPolynomial.X ((j.insertNth (α := fun _ => Fin m) p.1 p.2) i)) else 0
      rw [hp]
    _ = increasingColoringSum (L + 1) m := rfl
    _ = MvPolynomial.esymm (Fin m) Q (L + 1) :=
      increasingColoringSum_eq_esymm (L + 1) m

theorem isolated_strictMono_sum (L m : ℕ) :
    (∑ z : Fin m, ∑ c : Fin L → Fin m,
      if StrictMono c then
        MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) =
      MvPolynomial.esymm (Fin m) Q 1 *
        MvPolynomial.esymm (Fin m) Q L := by
  calc
    (∑ z : Fin m, ∑ c : Fin L → Fin m,
        if StrictMono c then
          MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) =
        (∑ z : Fin m, MvPolynomial.X z) *
          ∑ c : Fin L → Fin m,
            if StrictMono c then ∏ i, MvPolynomial.X (c i) else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : StrictMono c <;> simp [h]
    _ = MvPolynomial.esymm (Fin m) Q 1 *
          increasingColoringSum L m := by
      rw [MvPolynomial.esymm_one]
      rfl
    _ = MvPolynomial.esymm (Fin m) Q 1 *
          MvPolynomial.esymm (Fin m) Q L := by
      rw [increasingColoringSum_eq_esymm]

/-- Each insertion position contributes the same elementary polynomial, with any weights. -/
theorem weighted_inserted_strictMono_sum (L m : ℕ) (w : Fin (L + 1) → XPoly m) :
    (∑ z : Fin m, ∑ c : Fin L → Fin m, ∑ j : Fin (L + 1),
      w j * (if StrictMono (j.insertNth z c) then
        MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0)) =
      (∑ j, w j) * MvPolynomial.esymm (Fin m) Q (L + 1) := by
  calc
    _ = ∑ z : Fin m, ∑ j : Fin (L + 1), ∑ c : Fin L → Fin m,
        w j * (if StrictMono (j.insertNth z c) then
          MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin (L + 1), ∑ z : Fin m, ∑ c : Fin L → Fin m,
        w j * (if StrictMono (j.insertNth z c) then
          MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin (L + 1), w j * MvPolynomial.esymm (Fin m) Q (L + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [← Finset.mul_sum]
      rw [inserted_strictMono_sum]
    _ = _ := by rw [Finset.sum_mul]

/-- A uniform correction by weighted insertion gaps has a two-term elementary expression. -/
theorem isolated_with_insertion_correction_sum
    (L m : ℕ) (w : Fin (L + 1) → XPoly m) :
    (∑ z : Fin m, ∑ c : Fin L → Fin m,
      ((if StrictMono c then MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0) +
        ∑ j : Fin (L + 1), w j * (if StrictMono (j.insertNth z c) then
          MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) else 0))) =
      MvPolynomial.esymm (Fin m) Q 1 * MvPolynomial.esymm (Fin m) Q L +
        (∑ j, w j) * MvPolynomial.esymm (Fin m) Q (L + 1) := by
  simp only [Finset.sum_add_distrib]
  rw [isolated_strictMono_sum, weighted_inserted_strictMono_sum]

end VerticalStripLLT.Circular

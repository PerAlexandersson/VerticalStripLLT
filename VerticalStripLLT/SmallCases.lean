import VerticalStripLLT.Coloring
import Mathlib.Tactic.Ring

/-! A first semantic slice: one vertex and the three ordinary size-two paths.

The unicellular relation below is proved for every finite alphabet directly
from the coloring sum, without defining LLT by recursion.
-/

namespace VerticalStripLLT

open scoped BigOperators
open SchroderPath

/-- Normalize the size-zero path independently of the manuscript's implicit convention. -/
theorem coloringLLT_empty (m : ℕ) : coloringLLT SchroderPath.empty m = 1 := by
  simp [coloringLLT, coloringWeight, admissible, ascentCount]

theorem coloringWeight_singleton {m : ℕ} (c : Fin 1 → Fin m) :
    coloringWeight singleton c = MvPolynomial.X (c 0) := by
  simp [coloringWeight, admissible, ascentCount]

theorem coloringWeight_strictPair {m : ℕ} (c : Fin 2 → Fin m) :
    coloringWeight strictPair c =
      if c 0 < c 1 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0 := by
  simp [coloringWeight, admissible, ascentCount, Fin.prod_univ_two]

theorem coloringWeight_normalPair {m : ℕ} (c : Fin 2 → Fin m) :
    coloringWeight normalPair c =
      (if c 0 < c 1 then MvPolynomial.C Polynomial.X else 1) *
        (MvPolynomial.X (c 0) * MvPolynomial.X (c 1)) := by
  by_cases h : c 0 < c 1 <;>
    simp [coloringWeight, admissible, ascentCount, Fin.prod_univ_two,
      Finset.filter_singleton, h]

theorem coloringWeight_disconnectedPair {m : ℕ} (c : Fin 2 → Fin m) :
    coloringWeight disconnectedPair c =
      MvPolynomial.X (c 0) * MvPolynomial.X (c 1) := by
  simp [coloringWeight, admissible, ascentCount, Fin.prod_univ_two]

/-- The local coloring identity underlying the size-two unicellular relation. -/
theorem coloringWeight_pair_relation {m : ℕ} (c : Fin 2 → Fin m) :
    coloringWeight normalPair c - coloringWeight disconnectedPair c =
      MvPolynomial.C (Polynomial.X - 1) * coloringWeight strictPair c := by
  rw [coloringWeight_normalPair, coloringWeight_disconnectedPair, coloringWeight_strictPair]
  by_cases h : c 0 < c 1
  · simp [h, map_sub]
    ring
  · simp [h]

/-- The manuscript's unicellular relation for `nnee`, `nene`, and `nde`,
uniformly in the number of variables. -/
theorem coloringLLT_pair_unicellular (m : ℕ) :
    coloringLLT normalPair m - coloringLLT disconnectedPair m =
      MvPolynomial.C (Polynomial.X - 1) * coloringLLT strictPair m := by
  simp only [coloringLLT, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => coloringWeight_pair_relation c

/-- The size-one initial condition, including the empty alphabet. -/
theorem coloringLLT_singleton (m : ℕ) :
    coloringLLT singleton m = evalElementary m (elementary 1) := by
  simp only [coloringLLT, coloringWeight_singleton, evalElementary_elementary,
    PNat.val_ofNat]
  rw [MvPolynomial.esymm_one]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin m))
    (fun c => (MvPolynomial.X (c 0) : XPoly m))
    (fun a => MvPolynomial.X a) (fun _ => rfl)

private theorem sum_colorings_two {m : ℕ} (f : Fin m → Fin m → XPoly m) :
    (∑ c : Fin 2 → Fin m, f (c 0) (c 1)) = ∑ a, ∑ b, f a b := by
  calc
    _ = ∑ p : Fin m × Fin m, f p.1 p.2 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin m)) (fun c => f (c 0) (c 1))
        (fun p => f p.1 p.2) (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem coloringLLT_strictPair_two :
    coloringLLT strictPair 2 = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp only [coloringLLT, coloringWeight_strictPair]
  rw [sum_colorings_two (fun a b => if a < b then MvPolynomial.X a * MvPolynomial.X b else 0)]
  simp [Fin.sum_univ_two]

theorem coloringLLT_normalPair_two :
    coloringLLT normalPair 2 =
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 +
        MvPolynomial.C (Polynomial.X + 1) * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  simp only [coloringLLT, coloringWeight_normalPair]
  rw [sum_colorings_two (fun a b =>
    (if a < b then MvPolynomial.C Polynomial.X else 1) * (MvPolynomial.X a * MvPolynomial.X b))]
  simp [Fin.sum_univ_two, map_add]
  ring

theorem coloringLLT_disconnectedPair_two :
    coloringLLT disconnectedPair 2 =
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 +
        2 * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  simp only [coloringLLT, coloringWeight_disconnectedPair]
  rw [sum_colorings_two (fun a b => MvPolynomial.X a * MvPolynomial.X b)]
  simp [Fin.sum_univ_two]
  ring

/-- A decorated base case interpreted in the chosen coefficient representation. -/
theorem coloringLLT_strictPair_eq_evalElementary_two :
    coloringLLT strictPair 2 = evalElementary 2 (elementary 2) := by
  rw [coloringLLT_strictPair_two, evalElementary_elementary]
  have h : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
  change MvPolynomial.X 0 * MvPolynomial.X 1 = MvPolynomial.esymm (Fin 2) Q 2
  rw [MvPolynomial.esymm, h]
  simp [Fin.prod_univ_two]

/-- The elementary expression suggested by the size-two unicellular reduction.
This is a small expression, not a definition of the general recursive invariant. -/
noncomputable def normalPairExpansion : EExpansion :=
  elementary 1 ^ 2 + MvPolynomial.C (Polynomial.X - 1) * elementary 2

/-- Agreement of the independently defined coloring sum and a formal elementary
expression in two variables. This is only the first slice of the semantic bridge. -/
theorem coloringLLT_normalPair_eq_evalElementary_two :
    coloringLLT normalPair 2 = evalElementary 2 normalPairExpansion := by
  have h : MvPolynomial.esymm (Fin 2) Q 2 = MvPolynomial.X 0 * MvPolynomial.X 1 := by
    simpa using coloringLLT_strictPair_eq_evalElementary_two.symm.trans
      coloringLLT_strictPair_two
  rw [coloringLLT_normalPair_two]
  simp only [normalPairExpansion, map_add, map_pow, map_mul, evalElementary_C,
    evalElementary_elementary, PNat.val_ofNat, MvPolynomial.esymm_one, h,
    Fin.sum_univ_two, map_sub, map_one]
  ring

end VerticalStripLLT

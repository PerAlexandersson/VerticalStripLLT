import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Examples.Diagrams
import VerticalStripLLT.Examples.PairColorings
import VerticalStripLLT.ShiftEvaluation
import Mathlib.Tactic.Ring

/-! Genuine circular examples with two opposite natural arcs, for every alphabet. -/

namespace VerticalStripLLT.Circular

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Diagram

@[simp] theorem twoEdge_zero_tail : (twoEdge 0).tail = 1 := rfl

@[simp] theorem twoEdge_one_tail : (twoEdge 1).tail = 0 := rfl

theorem twoEdge_ne : twoEdge 0 ≠ twoEdge 1 := by
  intro h
  have h' := congrArg Edge.head h
  exact Fin.zero_ne_one h'

theorem univ_twoEdges : (Finset.univ : Finset (Edge constantAreaOne)) =
    {twoEdge 0, twoEdge 1} := by
  classical
  ext e
  rcases e with ⟨⟨i, j⟩, h⟩
  fin_cases i <;> fin_cases j <;> simp_all [constantAreaOne, twoEdge, Edge]
  all_goals exact (Nat.lt_irrefl 0) h.1

theorem coloringWeight_oneStrict {m : ℕ} (c : Fin 2 → Fin m) :
    oneStrict.edgeData.coloringWeight c =
      if c 0 < c 1 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0 := by
  classical
  by_cases h : c 0 < c 1
  · have h' : ¬ c 1 < c 0 := (asymm h)
    simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, EdgeData.ascentEdges,
      EdgeData.normalEdges, EdgeData.monomial, edgeData, oneStrict, twoCycle,
      univ_twoEdges, h, h', twoEdge_ne, Fin.prod_univ_two,
      Finset.filter_singleton]
  · simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, edgeData,
      oneStrict, twoCycle, h]

theorem coloringWeight_bothStrict {m : ℕ} (c : Fin 2 → Fin m) :
    bothStrict.edgeData.coloringWeight c = 0 := by
  classical
  have h : ¬ (c 1 < c 0 ∧ c 0 < c 1) := fun h => (asymm h.1) h.2
  simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, edgeData,
    bothStrict, twoCycle, Fin.univ_succ, h]

theorem coloringWeight_noStrict {m : ℕ} (c : Fin 2 → Fin m) :
    noStrict.edgeData.coloringWeight c =
      MvPolynomial.X (c 0) * MvPolynomial.X (c 1) +
        MvPolynomial.C (Polynomial.X - 1) *
          ((if c 0 < c 1 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0) +
           (if c 1 < c 0 then MvPolynomial.X (c 0) * MvPolynomial.X (c 1) else 0)) := by
  classical
  rcases lt_trichotomy (c 0) (c 1) with h | h | h
  · have h' : ¬ c 1 < c 0 := asymm h
    simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, EdgeData.ascentEdges,
      EdgeData.normalEdges, EdgeData.monomial, edgeData, noStrict, twoCycle,
      univ_twoEdges, h, h', Fin.prod_univ_two, map_sub,
      Finset.filter_insert, Finset.filter_singleton]
    ring
  · simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, EdgeData.ascentEdges,
      EdgeData.normalEdges, EdgeData.monomial, edgeData, noStrict, twoCycle,
      univ_twoEdges, h, Fin.prod_univ_two,
      Finset.filter_insert, Finset.filter_singleton]
  · have h' : ¬ c 0 < c 1 := asymm h
    simp [EdgeData.coloringWeight, EdgeData.admissibleColoring, EdgeData.ascentEdges,
      EdgeData.normalEdges, EdgeData.monomial, edgeData, noStrict, twoCycle,
      univ_twoEdges, h, h', Fin.prod_univ_two, map_sub,
      Finset.filter_insert, Finset.filter_singleton]
    ring

/-- The decorated one-strict-arc base case, uniformly in the alphabet. -/
theorem coloringLLT_oneStrict (m : ℕ) :
    oneStrict.coloringLLT m = evalElementary m (elementary 2) := by
  simp only [Diagram.coloringLLT, EdgeData.coloringLLT, coloringWeight_oneStrict]
  rw [sum_pair_strict, evalElementary_elementary]
  rfl

/-- A full strict circular cycle has no admissible coloring. -/
theorem coloringLLT_bothStrict (m : ℕ) : bothStrict.coloringLLT m = 0 := by
  simp [Diagram.coloringLLT, EdgeData.coloringLLT, coloringWeight_bothStrict]

theorem coloringLLT_noStrict (m : ℕ) :
    noStrict.coloringLLT m =
      evalElementary m (elementary 1 ^ 2 +
        MvPolynomial.C (2 * (Polynomial.X - 1)) * elementary 2) := by
  simp only [Diagram.coloringLLT, EdgeData.coloringLLT, coloringWeight_noStrict,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_pair_unrestricted, sum_pair_strict, sum_pair_reverse_strict]
  simp only [map_add, map_pow, map_mul, evalElementary_C, evalElementary_elementary]
  norm_num
  simp only [map_ofNat]
  ring

/-- The smallest circular shifted elementary expansion has two copies of q e₂. -/
theorem coloringLLT_noStrict_shifted (m : ℕ) :
    xQShift m (noStrict.coloringLLT m) =
      evalElementary m (elementary 1 ^ 2 +
        MvPolynomial.C (2 * Polynomial.X) * elementary 2) := by
  rw [coloringLLT_noStrict, ← evalElementary_qShiftMap]
  congr 1
  simp [qShiftMap, qShift, elementary, Polynomial.X_comp]

end VerticalStripLLT.Circular

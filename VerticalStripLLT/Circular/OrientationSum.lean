import VerticalStripLLT.Circular.EdgeColoring
import VerticalStripLLT.Circular.SubsetExpansion
import VerticalStripLLT.ShiftEvaluation

/-! The shifted coloring sum as a sum over selected non-strict edge sets. -/

namespace VerticalStripLLT.Circular

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace EdgeData

variable {V E : Type*}

private theorem xQShift_monomial [Fintype V] {m : ℕ} (c : V → Fin m) :
    xQShift m (monomial c) = monomial c := by
  simp [xQShift, monomial]

private theorem xQShift_C_X_pow (m k : ℕ) :
    xQShift m (MvPolynomial.C (Polynomial.X ^ k) : XPoly m) =
      MvPolynomial.C ((Polynomial.X + 1) ^ k) := by
  rw [xQShift, MvPolynomial.map_C, map_pow]
  congr 1
  simp [qShift, Polynomial.coe_compRingHom_apply]

private theorem C_X_add_one (m : ℕ) :
    (MvPolynomial.C Polynomial.X + 1 : XPoly m) = MvPolynomial.C (Polynomial.X + 1) := by
  simp

private theorem C_X_pow (m k : ℕ) :
    (MvPolynomial.C Polynomial.X : XPoly m) ^ k = MvPolynomial.C (Polynomial.X ^ k) := by
  simp

/-- Before removing cyclic selected sets, the shifted LLT coloring sum expands over all
subsets of the non-strict edge instances. -/
theorem xQShift_coloringLLT_eq_all_selected
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeData V E) (m : ℕ) :
    xQShift m (G.coloringLLT m) =
      ∑ A ∈ G.normalEdges.powerset,
        MvPolynomial.C (Polynomial.X ^ A.card) * G.strictOrderEnumerator A m := by
  classical
  calc
    xQShift m (G.coloringLLT m) =
        ∑ c : V → Fin m, xQShift m (G.coloringWeight c) := by
      rw [coloringLLT, map_sum]
    _ = ∑ c : V → Fin m,
        if G.admissibleColoring c then
          (MvPolynomial.C Polynomial.X + 1) ^
              (G.normalEdges.filter fun e => c (G.tail e) < c (G.head e)).card * monomial c
        else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : G.admissibleColoring c
      · simp only [coloringWeight, hc, ite_true, map_mul]
        rw [xQShift_C_X_pow, xQShift_monomial, map_pow, ← C_X_add_one]
        rfl
      · simp [coloringWeight, hc]
    _ = ∑ A ∈ G.normalEdges.powerset,
        (MvPolynomial.C Polynomial.X : XPoly m) ^ A.card *
          ∑ c : V → Fin m,
            if G.admissibleColoring c ∧
                (∀ e ∈ A, c (G.tail e) < c (G.head e)) then monomial c else 0 := by
      have hexp := @finite_subset_coloring_expansion (V → Fin m) E (XPoly m)
        inferInstance inferInstance inferInstance
        G.normalEdges (fun c => G.admissibleColoring c)
        (fun c e => c (G.tail e) < c (G.head e))
        (fun c => Classical.propDecidable (G.admissibleColoring c))
        (fun c e => inferInstance)
        (fun c => monomial c) (MvPolynomial.C Polynomial.X)
      convert hexp using 1
      apply Finset.sum_congr rfl
      intro A _
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
    _ = ∑ A ∈ G.normalEdges.powerset,
        MvPolynomial.C (Polynomial.X ^ A.card) * G.strictOrderEnumerator A m := by
      apply Finset.sum_congr rfl
      intro A _
      rw [C_X_pow]
      congr 1
      unfold strictOrderEnumerator
      apply Finset.sum_congr rfl
      intro c _
      have hconditions :
          (G.admissibleColoring c ∧ ∀ e ∈ A, c (G.tail e) < c (G.head e)) ↔
            ∀ e ∈ G.strict ∪ A, c (G.tail e) < c (G.head e) := by
        constructor
        · rintro ⟨hstrict, hA⟩ e he
          rcases Finset.mem_union.mp he with he | he
          · exact hstrict e he
          · exact hA e he
        · intro h
          constructor
          · intro e he
            exact h e (Finset.mem_union_left _ he)
          · intro e he
            exact h e (Finset.mem_union_right _ he)
      simp only [hconditions]
      split_ifs <;> rfl

/-- Cyclic selected sets vanish, leaving the admissible selected-edge orientations. -/
theorem xQShift_coloringLLT_eq_orientation_sum
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeData V E) (m : ℕ) :
    xQShift m (G.coloringLLT m) =
      ∑ A ∈ G.normalEdges.powerset.filter (G.Admissible),
        MvPolynomial.C (Polynomial.X ^ A.card) * G.strictOrderEnumerator A m := by
  classical
  rw [G.xQShift_coloringLLT_eq_all_selected m, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : G.Admissible A
  · simp [hA]
  · simp [hA, G.strictOrderEnumerator_eq_zero_of_not_admissible A hA m]

end EdgeData
end VerticalStripLLT.Circular

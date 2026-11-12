import VerticalStripLLT.CyclicHessenberg.SortedLoopBijection
import VerticalStripLLT.CyclicHessenberg.MatchingExpansion

/-! The composition-sorted and canonical colored-loop sums agree with their original weights. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n m : ℕ}

theorem coloredLoopAscentCount_eq_orderedLoopAscentCount (h : Tuple k n)
    (L : LoopCover h) (κ : Fin k → Fin m) :
    coloredLoopAscentCount h L κ = orderedLoopAscentCount h (L, colorSortedPerm κ) := by
  classical
  let e : (Fin n × Fin k × Fin k) ≃ (Fin n × Fin k × Fin k) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (colorSortedPerm κ) (colorSortedPerm κ))
  apply (Finset.card_equiv e ?_).symm
  rintro ⟨ℓ, i, j⟩
  simp only [orderedLoopAscentEvents, loopAscentEvents,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [orderedLoopValue, e, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  rw [← colorSortedPerm_precedes_iff_lt]
  tauto

noncomputable def sortedLoopColorWeight (h : Tuple k n)
    (x : SortedLoopColorData h m) : XPoly m :=
  MvPolynomial.C (Polynomial.X ^ orderedLoopAscentCount h x.2.1.val) *
    ∏ i : Fin k, MvPolynomial.X (x.2.2.val i)

theorem sortedLoopColorWeight_sort (h : Tuple k n)
    (x : LoopCover h × (Fin k → Fin m)) :
    sortedLoopColorWeight h (sortColoredLoop h x) =
      MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h x.1 x.2) *
        ∏ a : Fin k, MvPolynomial.X (x.2 a) := by
  change MvPolynomial.C (Polynomial.X ^
    orderedLoopAscentCount h (x.1, colorSortedPerm x.2)) *
      ∏ i : Fin k, MvPolynomial.X (x.2 (colorSortedPerm x.2 i)) = _
  rw [← coloredLoopAscentCount_eq_orderedLoopAscentCount]
  rw [Equiv.prod_comp (colorSortedPerm x.2) (fun a => (MvPolynomial.X (x.2 a) : XPoly m))]

theorem sortedLoopColoringSum_eq_sum_weight (h : Tuple k n) (m : ℕ) :
    sortedLoopColoringSum h m = ∑ x : SortedLoopColorData h m, sortedLoopColorWeight h x := by
  classical
  simp only [sortedLoopColoringSum, runMonomialQuasisymmetric, Finset.mul_sum,
    Fintype.sum_sigma, Fintype.sum_prod_type, sortedLoopColorWeight]

/-- Exact weighted source bridge, before the substitution in `q`. -/
theorem loopColoringLLT_eq_sortedLoopColoringSum (h : Tuple k n) (m : ℕ) :
    loopColoringLLT h m = sortedLoopColoringSum h m := by
  classical
  rw [sortedLoopColoringSum_eq_sum_weight,
    ← (coloredLoopSortedEquiv h).sum_comp (sortedLoopColorWeight h)]
  simp only [coloredLoopSortedEquiv, Equiv.coe_fn_mk, sortedLoopColorWeight_sort,
    Fintype.sum_prod_type, loopColoringLLT]

theorem shift_sortedLoopColoringSum_eq_cyclicExpansion (h : Tuple k n)
    (hn : 0 < n) (m : ℕ) :
    xQShift m (sortedLoopColoringSum h m) = evalElementary m (cyclicExpansion h) := by
  rw [← loopColoringLLT_eq_sortedLoopColoringSum]
  exact shift_loopColoringLLT_eq_cyclicExpansion h hn m

end VerticalStripLLT.CyclicHessenberg

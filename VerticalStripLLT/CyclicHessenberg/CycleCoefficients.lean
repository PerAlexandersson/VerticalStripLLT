import VerticalStripLLT.CyclicHessenberg.CycleExpansion

/-! Coefficients of the literal canonical-cycle expansion. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The coefficient at `d` is supported on displays of shape `d`, with the
remaining power of `X` determined by the number of displayed blocks. -/
theorem naturalCycleSum_coeff (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) (d : ℕ+ →₀ ℕ) :
    (naturalCycleSum S Z).coeff d =
      Polynomial.X ^ (S.card - d.sum (fun _ n => n)) *
        ∑ D : CycleDisplay S,
          if D.shape = d then Z D.source.val D.target.val else 0 := by
  classical
  unfold naturalCycleSum
  simp only [MvPolynomial.coeff_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [cycleWeight, CycleDisplay.elementaryMonomial_eq_monomial,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  by_cases hs : D.shape = d
  · have hdeg : D.count = d.sum (fun _ n => n) := by
      calc
        D.count = D.shape.sum (fun _ n => n) :=
          (CycleDisplay.shape_degree D).symm
        _ = d.sum (fun _ n => n) := by rw [hs]
    simp [hs, hdeg]
  · simp [hs]

/-- A shape whose weighted size is not the size of `S` has zero coefficient. -/
theorem naturalCycleSum_coeff_eq_zero_of_weight_ne (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) (d : ℕ+ →₀ ℕ)
    (hd : d.sum (fun i n => i.val * n) ≠ S.card) :
    (naturalCycleSum S Z).coeff d = 0 := by
  rw [naturalCycleSum_coeff]
  have hsum :
      (∑ D : CycleDisplay S,
        if D.shape = d then Z D.source.val D.target.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro D hD
    split_ifs with hs
    · have hweight : d.sum (fun i n => i.val * n) = S.card := by
        rw [← hs]
        exact CycleDisplay.shape_weight D
      exact (hd hweight).elim
    · simp
  rw [hsum]
  simp

end VerticalStripLLT.CyclicHessenberg

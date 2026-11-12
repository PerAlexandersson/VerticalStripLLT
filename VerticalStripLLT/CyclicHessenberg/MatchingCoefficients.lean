import VerticalStripLLT.CyclicHessenberg.MatchingExpansion
import VerticalStripLLT.CyclicHessenberg.MarkedWeights
import VerticalStripLLT.CyclicHessenberg.CycleCoefficients

/-! Coefficient factors and a literal finite marked-ascent counting interpretation. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n : ℕ}

theorem matchingShape_degree (h : Tuple k n) (φ : MatchingTuple h) :
    (matchingShape h φ).sum (fun _ a => a) = matchingCycleCount h φ :=
  (matchingDisplay h φ).shape_degree

theorem matchingShape_weight (h : Tuple k n) (φ : MatchingTuple h) :
    (matchingShape h φ).sum (fun i a => i.val * a) = k := by
  simpa only [matchingShape, Finset.card_univ, Fintype.card_fin] using
    (matchingDisplay h φ).shape_weight

/-- A fixed shape has the forced power `q^(k-number of parts)` as a factor. -/
theorem naturalCyclicExpansion_coeff (h : Tuple k n) (d : ℕ+ →₀ ℕ) :
    (naturalCyclicExpansion h).coeff d =
      Polynomial.X ^ (k - d.sum (fun _ a => a)) *
        ∑ φ : MatchingTuple h,
          if matchingShape h φ = d then (1 + Polynomial.X) ^ matchingAscentCount h φ else 0 := by
  classical
  simp only [naturalCyclicExpansion, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro φ hφ
  by_cases hd : matchingShape h φ = d
  · have hdeg : matchingCycleCount h φ = d.sum (fun _ a => a) := by
      rw [← hd]
      exact (matchingShape_degree h φ).symm
    simp [hd, hdeg]
  · simp [hd]

/-- Events selected from a matching keep their actual layer and canonical positions. -/
noncomputable def admissibleMarkings (h : Tuple k n) (φ : MatchingTuple h)
    (d : ℕ+ →₀ ℕ) (j : ℕ) : Finset (Finset (Fin n × LayerPosition k × LayerPosition k)) := by
  classical
  exact (matchingAscentEvents h φ).powerset.filter fun T =>
    matchingShape h φ = d ∧ j = (k - matchingCycleCount h φ) + T.card

abbrev MarkedMatching (h : Tuple k n) (d : ℕ+ →₀ ℕ) (j : ℕ) :=
  Σ φ : MatchingTuple h, ↥(admissibleMarkings h φ d j)

noncomputable instance markedMatchingFintype (h : Tuple k n) (d : ℕ+ →₀ ℕ) (j : ℕ) :
    Fintype (MarkedMatching h d j) := inferInstanceAs (Fintype (Sigma _))

/-- Every natural elementary/q coefficient counts actual matchings with marked ascent subsets. -/
theorem naturalCyclicExpansion_coeff_eq_card_markedMatching (h : Tuple k n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    ((naturalCyclicExpansion h).coeff d).coeff j = Fintype.card (MarkedMatching h d j) := by
  classical
  rw [Fintype.card_sigma]
  simp only [naturalCyclicExpansion, MvPolynomial.coeff_sum, Polynomial.finset_sum_coeff,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro φ hφ
  by_cases hd : matchingShape h φ = d
  · simp only [hd, ite_true, mul_one, admissibleMarkings, true_and, Fintype.card_coe]
    exact coeff_X_pow_mul_one_add_X_pow_card (matchingAscentEvents h φ)
      (k - matchingCycleCount h φ) j
  · simp [hd, admissibleMarkings]

theorem cyclicExpansion_coeff_eq_card_markedMatching (h : Tuple k n)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    ((cyclicExpansion h).coeff d).coeff j = (Fintype.card (MarkedMatching h d j) : ℤ) := by
  simp only [cyclicExpansion, naturalCast, MvPolynomial.coeff_map,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [naturalCyclicExpansion_coeff_eq_card_markedMatching]
  rfl

theorem naturalCyclicExpansion_coeff_eq_zero_of_weight_ne (h : Tuple k n)
    (d : ℕ+ →₀ ℕ) (hd : d.sum (fun i a => i.val * a) ≠ k) :
    (naturalCyclicExpansion h).coeff d = 0 := by
  rw [← naturalCanonicalCyclicExpansion_eq_matchingExpansion]
  apply naturalCycleSum_coeff_eq_zero_of_weight_ne
  simpa only [Finset.card_univ, Fintype.card_fin] using hd

end VerticalStripLLT.CyclicHessenberg

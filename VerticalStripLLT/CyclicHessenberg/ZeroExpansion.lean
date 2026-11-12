import VerticalStripLLT.CyclicHessenberg.IdentityMatching
import VerticalStripLLT.CyclicHessenberg.SingletonCycles
import VerticalStripLLT.CyclicHessenberg.LoopMatchings

/-! The paper's zero-parameter check directly in the formal elementary basis. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n : ℕ}

theorem matchingCycleCount_eq_size_iff (h : Tuple k n) (φ : MatchingTuple h) :
    matchingCycleCount h φ = k ↔ matchingMonodromy φ.val = 1 := by
  constructor
  · intro hc
    have hh := (matchingDisplay h φ).fullPerm_eq_one_of_count_eq_card hc
    simpa only [matchingDisplay, fullPerm_permutationDisplay] using hh
  · intro hp
    simp only [matchingCycleCount, matchingDisplay, hp, permutationDisplay_one_count]

/-- At `q=0`, only singleton-cycle matchings survive. Their number is the loop-cover count. -/
theorem naturalCyclicExpansion_at_zero (h : Tuple k n) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : ℕ)) (naturalCyclicExpansion h) =
      (Fintype.card (LoopCover h) : MvPolynomial ℕ+ ℕ) * MvPolynomial.X 1 ^ k := by
  classical
  let M : MvPolynomial ℕ+ ℕ := MvPolynomial.X 1 ^ k
  have hterm (φ : MatchingTuple h) :
      MvPolynomial.map (Polynomial.evalRingHom (0 : ℕ))
        (MvPolynomial.C (Polynomial.X ^ (k - matchingCycleCount h φ) *
          (1 + Polynomial.X) ^ matchingAscentCount h φ) *
            MvPolynomial.monomial (matchingShape h φ) 1) =
        if matchingMonodromy φ.val = 1 then M else 0 := by
    by_cases hp : matchingMonodromy φ.val = 1
    · have hc := (matchingCycleCount_eq_size_iff h φ).mpr hp
      have hs : matchingShape h φ = Finsupp.single 1 k := by
        simp only [matchingShape, matchingDisplay, hp, permutationDisplay_one_shape]
      simp [hp, hc, hs, M, MvPolynomial.X_pow_eq_monomial]
    · have hne : k - matchingCycleCount h φ ≠ 0 := by
        have hle : matchingCycleCount h φ ≤ k := by
          simpa only [matchingCycleCount, Finset.card_univ, Fintype.card_fin]
            using (matchingDisplay h φ).count_le_card
        have hnot : matchingCycleCount h φ ≠ k :=
          mt (matchingCycleCount_eq_size_iff h φ).mp hp
        lia
      simp [hp, hne]
  simp only [naturalCyclicExpansion, map_sum, hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype (fun φ : MatchingTuple h => matchingMonodromy φ.val = 1)]
  rw [← card_loopCover_eq_card_identityMatchingFiber h]

end VerticalStripLLT.CyclicHessenberg

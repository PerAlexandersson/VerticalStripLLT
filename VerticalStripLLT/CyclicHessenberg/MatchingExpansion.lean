import VerticalStripLLT.CyclicHessenberg.CanonicalMatching
import VerticalStripLLT.CyclicHessenberg.OpenPathWeight
import VerticalStripLLT.CyclicHessenberg.CyclePositivity

/-! Reindex the explicit cycle/path formula by actual feasible matching tuples. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n : ℕ}

noncomputable def displayMatchingFiberEquiv (h : Tuple k n)
    (D : CycleDisplay (Finset.univ : Finset (Fin k))) :
    MatchingFiber h D.fullPerm ≃ OpenLayerPath h D.source D.target :=
  (Equiv.subtypeEquivRight (fun φ : MatchingTuple h => by
    rw [D.fullPerm_eq_boundaryRatio])).trans (matchingOpenPathEquiv h D.source D.target)

/-- A canonical cycle display together with an open path is exactly a matching tuple. -/
noncomputable def canonicalPathMatchingEquiv (h : Tuple k n) :
    (Σ D : CycleDisplay (Finset.univ : Finset (Fin k)),
      OpenLayerPath h D.source D.target) ≃ MatchingTuple h :=
  (Equiv.sigmaCongrRight (fun D => (displayMatchingFiberEquiv h D).symm)).trans
    ((Equiv.sigmaCongrLeft (cycleDisplayEquivPerm (V := Fin k))).trans
      (Equiv.sigmaFiberEquiv (fun φ : MatchingTuple h => matchingMonodromy φ.val)))

theorem canonicalPathMatchingEquiv_symm (h : Tuple k n) (φ : MatchingTuple h) :
    (canonicalPathMatchingEquiv h).symm φ =
      ⟨matchingDisplay h φ, matchingCanonicalPath h φ⟩ := by
  apply (canonicalPathMatchingEquiv h).injective
  rw [Equiv.apply_symm_apply]
  symm
  change (openPathToMatching h _ _ (matchingToOpenPath h _ _ _)).val = φ
  exact congrArg Subtype.val ((matchingOpenPathEquiv h _ _).left_inv _)

/-- The canonical-cycle expansion is the direct sum over feasible matchings. -/
theorem naturalCanonicalCyclicExpansion_eq_matchingExpansion (h : Tuple k n) :
    naturalCanonicalCyclicExpansion h = naturalCyclicExpansion h := by
  classical
  let F : (Σ D : CycleDisplay (Finset.univ : Finset (Fin k)),
      OpenLayerPath h D.source D.target) → NEExpansion := fun x =>
    MvPolynomial.C (Polynomial.X ^ (k - x.1.count) *
      (1 + Polynomial.X) ^ (∑ ℓ : Fin n,
        layerAscentCount (h ℓ) (x.2.val ℓ.castSucc) (x.2.val ℓ.succ))) *
      x.1.elementaryMonomial
  have hexpand : naturalCanonicalCyclicExpansion h = ∑ x, F x := by
    rw [Fintype.sum_sigma]
    unfold naturalCanonicalCyclicExpansion naturalCycleSum
    apply Finset.sum_congr rfl
    intro D hD
    simp only [cycleWeight, kernelEntry_order, naturalOpenKernel_eq_openLayerPath_sum,
      Finset.card_univ, Fintype.card_fin, Finset.mul_sum, map_sum, Finset.sum_mul, F]
  rw [hexpand, ← (canonicalPathMatchingEquiv h).symm.sum_comp F]
  unfold naturalCyclicExpansion
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [canonicalPathMatchingEquiv_symm]
  simp only [F, matchingAscentCount_eq_sum, matchingCycleCount, matchingShape,
    CycleDisplay.elementaryMonomial_eq_monomial]

theorem shift_loopColoringLLT_eq_cyclicExpansion (h : Tuple k n) (hn : 0 < n) (m : ℕ) :
    xQShift m (loopColoringLLT h m) = evalElementary m (cyclicExpansion h) := by
  change xQShift m (loopColoringLLT h m) =
    evalElementary m (naturalCast (naturalCyclicExpansion h))
  rw [← naturalCanonicalCyclicExpansion_eq_matchingExpansion]
  exact shift_loopColoringLLT_eq_canonicalCycleExpansion h hn m

theorem cyclicExpansion_coeff_nonneg (h : Tuple k n) (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((cyclicExpansion h).coeff d).coeff j := by
  change 0 ≤ ((naturalCast (naturalCyclicExpansion h)).coeff d).coeff j
  rw [← naturalCanonicalCyclicExpansion_eq_matchingExpansion]
  exact canonicalCyclicExpansion_coeff_nonneg h d j

theorem cyclicExpansion_isWeightedHomogeneous (h : Tuple k n) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val) (cyclicExpansion h) k := by
  change MvPolynomial.IsWeightedHomogeneous _ (naturalCast (naturalCyclicExpansion h)) k
  rw [← naturalCanonicalCyclicExpansion_eq_matchingExpansion]
  exact canonicalCyclicExpansion_isWeightedHomogeneous h

end VerticalStripLLT.CyclicHessenberg

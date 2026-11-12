import VerticalStripLLT.CyclicHessenberg.CycleEquiv
import VerticalStripLLT.CyclicHessenberg.MatchingPaths
import VerticalStripLLT.CyclicHessenberg.LayerExchangeCounts

/-! Canonical cycle order and layer-labelled ascents of an actual matching tuple. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n : ℕ}

theorem CycleDisplay.fullPerm_eq_boundaryRatio
    (D : CycleDisplay (Finset.univ : Finset (Fin k))) :
    D.fullPerm = (fullOrdersPerm k D.source).symm.trans (fullOrdersPerm k D.target) := by
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := (fullOrdersPerm k D.source).surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  let j := (layerPositionEquiv k).symm i
  have hs : fullOrdersPerm k D.source i = (orderEquiv D.source j).val := by
    simpa [j] using fullOrdersPerm_apply_position D.source j
  have ht : fullOrdersPerm k D.target i = (orderEquiv D.target j).val := by
    simpa [j] using fullOrdersPerm_apply_position D.target j
  rw [hs, ht]
  exact congrArg Subtype.val (D.toPerm_apply_source j)

noncomputable def matchingDisplay (h : Tuple k n) (φ : MatchingTuple h) :
    CycleDisplay (Finset.univ : Finset (Fin k)) :=
  permutationDisplay (matchingMonodromy φ.val)

noncomputable def matchingCanonicalPath (h : Tuple k n) (φ : MatchingTuple h) :
    OpenLayerPath h (matchingDisplay h φ).source (matchingDisplay h φ).target :=
  matchingToOpenPath h _ _ ⟨φ,
    (fullPerm_permutationDisplay (matchingMonodromy φ.val)).symm.trans
      (matchingDisplay h φ).fullPerm_eq_boundaryRatio⟩

noncomputable def matchingShape (h : Tuple k n) (φ : MatchingTuple h) : ℕ+ →₀ ℕ :=
  (matchingDisplay h φ).shape

noncomputable def matchingCycleCount (h : Tuple k n) (φ : MatchingTuple h) : ℕ :=
  (matchingDisplay h φ).count

/-- Ascent occurrences retain the layer and both canonical strand positions. -/
noncomputable def matchingAscentEvents (h : Tuple k n) (φ : MatchingTuple h) :
    Finset (Fin n × LayerPosition k × LayerPosition k) := by
  classical
  let P := matchingCanonicalPath h φ
  exact Finset.univ.filter fun e => e.2.1 < e.2.2 ∧
    (orderEquiv (P.val e.1.castSucc) e.2.1).val <
      (orderEquiv (P.val e.1.castSucc) e.2.2).val ∧
    (orderEquiv (P.val e.1.castSucc) e.2.2).val ≤
      h e.1 (orderEquiv (P.val e.1.succ) e.2.1).val

noncomputable def matchingAscentCount (h : Tuple k n) (φ : MatchingTuple h) : ℕ :=
  (matchingAscentEvents h φ).card

theorem matchingAscentCount_eq_sum (h : Tuple k n) (φ : MatchingTuple h) :
    matchingAscentCount h φ = ∑ ℓ : Fin n,
      layerAscentCount (h ℓ) ((matchingCanonicalPath h φ).val ℓ.castSucc)
        ((matchingCanonicalPath h φ).val ℓ.succ) := by
  classical
  simp only [matchingAscentCount, matchingAscentEvents, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type, layerAscentCount_eq_sum]

/-- The final natural expression is the explicit sum over feasible matching tuples. -/
noncomputable def naturalCyclicExpansion (h : Tuple k n) : NEExpansion :=
  ∑ φ : MatchingTuple h,
    MvPolynomial.C (Polynomial.X ^ (k - matchingCycleCount h φ) *
      (1 + Polynomial.X) ^ matchingAscentCount h φ) *
      MvPolynomial.monomial (matchingShape h φ) 1

noncomputable def cyclicExpansion (h : Tuple k n) : EExpansion :=
  naturalCast (naturalCyclicExpansion h)

end VerticalStripLLT.CyclicHessenberg

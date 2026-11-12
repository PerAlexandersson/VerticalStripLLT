import VerticalStripLLT.CyclicHessenberg.Source
import VerticalStripLLT.CyclicHessenberg.MatchingCoefficients

/-!
# Elementary positivity of cyclic LLT polynomials

We formalize the cyclic LLT polynomials introduced by Donghyun Kim and Jaeseong Oh in
*The elliptic Hall algebra and the combinatorics of affine Springer fibers*,
[arXiv:2611.14177v1](https://arxiv.org/abs/2611.14177v1), Section 6.

For a tuple `h` of `n > 0` Hessenberg functions on `k` vertices, we prove

`cLLT_h(X; q+1) = ∑ φ, q^(k-c(φ)) (1+q)^A(φ) e_{λ(φ)}(X)`.

Here `φ` ranges over feasible perfect matchings at the layer interfaces. The composed
matching has `c(φ)` cycles with length partition `λ(φ)`, and `A(φ)` counts ascents in
canonical cycle order. Thus every elementary coefficient is a polynomial in `ℕ[q]`.
The same expansion evaluates to the source polynomial in every finite alphabet.

The proof follows the loop/coloring model, transfer-kernel exchange, positive root
deletion, and canonical cycle expansion. The five theorems below give the source
identification, cycle and matching formulas, marked-ascent coefficient counts,
and elementary positivity.
-/

namespace VerticalStripLLT.Challenges.CyclicHessenberg

open VerticalStripLLT.CyclicHessenberg

variable {k n : ℕ}

/-- Exact source equality, including the empty support and empty alphabet. -/
theorem sortedLoopModel (h : Tuple k n) (m : ℕ) :
    cyclicLLT h m = loopColoringLLT h m :=
  cyclicLLT_eq_loopColoringLLT h m

/-- Positive root deletion unrolls into the canonical-cycle elementary expansion. -/
theorem positiveCycleExpansion (h : Tuple k n) (hn : 0 < n) (m : ℕ) :
    xQShift m (cyclicLLT h m) = evalElementary m (canonicalCyclicExpansion h) := by
  rw [cyclicLLT_eq_loopColoringLLT]
  exact shift_loopColoringLLT_eq_canonicalCycleExpansion h hn m

/-- The cycle formula is the explicit sum over feasible layer matchings. -/
theorem positiveMatchingExpansion (h : Tuple k n) (hn : 0 < n) (m : ℕ) :
    xQShift m (cyclicLLT h m) = evalElementary m (cyclicExpansion h) :=
  shift_cyclicLLT_eq_cyclicExpansion h hn m

/-- Every elementary/q coefficient counts matchings with marked ascent events. -/
theorem elementaryCoefficientFormula (h : Tuple k n) (d : ℕ+ →₀ ℕ) (j : ℕ) :
    ((cyclicExpansion h).coeff d).coeff j = (Fintype.card (MarkedMatching h d j) : ℤ) :=
  cyclicExpansion_coeff_eq_card_markedMatching h d j

/-- A single explicit natural-coefficient elementary expansion works in every finite alphabet. -/
theorem ePositive (h : Tuple k n) (hn : 0 < n) :
    (∀ m : ℕ, xQShift m (cyclicLLT h m) =
      evalElementary m (naturalCast (naturalCyclicExpansion h))) ∧
    (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ ((cyclicExpansion h).coeff d).coeff j) ∧
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val) (cyclicExpansion h) k :=
  ⟨shift_cyclicLLT_eq_cyclicExpansion h hn, cyclicExpansion_coeff_nonneg h,
    cyclicExpansion_isWeightedHomogeneous h⟩

end VerticalStripLLT.Challenges.CyclicHessenberg

import VerticalStripLLT.Circular.Flip
import VerticalStripLLT.Circular.HRVPositive
import VerticalStripLLT.Circular.HRVDegree

/-! Positivity and weighted degree for actual circular component HRV sums. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The natural-coefficient version of one complete component HRV sum. -/
noncomputable def naturalComponentHRV (D : Diagram n) (θ : Orientation D) :
    NatEExpansion :=
  ∑ η ∈ flipComponent D θ, naturalHRVMonomial η

/-- The common ascent-weighted component HRV expression. -/
noncomputable def weightedComponentHRV (D : Diagram n) (θ : Orientation D) :
    EExpansion :=
  MvPolynomial.C (Polynomial.X ^ θ.val.card) * componentHRV D θ

theorem naturalCast_naturalComponentHRV (D : Diagram n) (θ : Orientation D) :
    naturalCast (naturalComponentHRV D θ) = componentHRV D θ := by
  classical
  unfold naturalComponentHRV componentHRV
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro η hη
  exact naturalCast_naturalHRVMonomial η

theorem componentHRV_coeff_nonneg (D : Diagram n) (θ : Orientation D)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((componentHRV D θ).coeff d).coeff j := by
  rw [← naturalCast_naturalComponentHRV D θ]
  simp only [naturalCast, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  exact Nat.cast_nonneg _

theorem weightedComponentHRV_coeff_nonneg (D : Diagram n) (θ : Orientation D)
    (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((weightedComponentHRV D θ).coeff d).coeff j := by
  rw [weightedComponentHRV, MvPolynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · exact componentHRV_coeff_nonneg D θ d (j - θ.val.card)
  · simp

theorem componentHRV_isWeightedHomogeneous_degree (D : Diagram n) (θ : Orientation D) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (componentHRV D θ) n := by
  unfold componentHRV
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro η hη
  exact Orientation.hrvMonomial_isWeightedHomogeneous_degree η

theorem weightedComponentHRV_isWeightedHomogeneous_degree
    (D : Diagram n) (θ : Orientation D) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (weightedComponentHRV D θ) n := by
  exact (componentHRV_isWeightedHomogeneous_degree D θ).C_mul
    (Polynomial.X ^ θ.val.card)

end

end VerticalStripLLT.Circular

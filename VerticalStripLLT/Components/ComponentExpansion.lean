import VerticalStripLLT.Components.OrdinaryComponentExpansion
import VerticalStripLLT.Components.ComponentPositive
import VerticalStripLLT.Components.CircularFromOrdinaryComponents

/-! The actual strict-coloring and HRV sums agree on every complete flip component. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n}

/-- The component HRV formula for every circular diagram and every finite alphabet. -/
theorem component_strict_eq_elementary (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  apply component_identity_of_forward_components θ m
  intro k E hforward η
  exact component_strict_eq_elementary_of_forward η hforward m

/-- Restore the common shifted q-weight, exposing the actual HRV sum. -/
theorem component_weighted_strict_eq_orientation_sum (θ : Orientation D) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    ∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * evalElementary m η.hrvMonomial := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary]
  simp only [componentHRV, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [card_eq_of_mem_flipComponent hη]

/-- A single formal elementary expression represents the weighted component in all alphabets. -/
theorem component_weighted_strict_eq_eval (θ : Orientation D) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    evalElementary m (weightedComponentHRV D θ) := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary]
  simp only [weightedComponentHRV, map_mul, evalElementary_C]

/-- Every complete circular component has a homogeneous elementary-positive expansion. -/
theorem component_weighted_e_positive (θ : Orientation D) :
    ∃ f : EExpansion,
      (∀ m, (∑ η ∈ flipComponent D θ,
        MvPolynomial.C (Polynomial.X ^ η.val.card) *
          D.edgeData.strictOrderEnumerator η.val m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n := by
  exact ⟨weightedComponentHRV D θ, component_weighted_strict_eq_eval θ,
    weightedComponentHRV_coeff_nonneg D θ,
    weightedComponentHRV_isWeightedHomogeneous_degree D θ⟩

end VerticalStripLLT.Circular

import VerticalStripLLT.Components.DiagramProof.Consequences
import VerticalStripLLT.Components.CircularFromOrdinaryComponents

/-!
# The circular component theorem by diagrams

The finite circular companion (`CircularFromOrdinaryComponents`) writes every whole
circular flip component as a signed union of whole components of forward diagrams.
Feeding it the ordinary theorem by diagrams gives the component HRV formula for
every circular diagram, every whole flip component and every finite alphabet.

The companion reduction does not use the word functional or the signed-sink
extraction, so these declarations use only the diagram route for the ordinary
input.
-/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

variable {n : ℕ} {D : Diagram n}

/-- **The circular component theorem, by diagrams.** -/
theorem component_strict_eq_elementary (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) :=
  component_identity_of_forward_components θ m fun _ hforward η =>
    component_strict_eq_elementary_of_forward η hforward m

/-- Restore the common shifted q-weight, exposing the actual HRV sum. -/
theorem component_weighted_strict_eq_orientation_sum (θ : Orientation D)
    (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    ∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * evalElementary m η.hrvMonomial := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary]
  simp only [componentHRV, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun η hη => by rw [card_eq_of_mem_flipComponent hη]

/-- One formal elementary expression represents the weighted component in all
alphabets. -/
theorem component_weighted_strict_eq_eval (θ : Orientation D) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    evalElementary m (weightedComponentHRV D θ) := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary]
  simp only [weightedComponentHRV, map_mul, evalElementary_C]

/-- Every whole circular component has a homogeneous elementary-positive expansion. -/
theorem component_weighted_e_positive (θ : Orientation D) :
    ∃ f : EExpansion,
      (∀ m, (∑ η ∈ flipComponent D θ,
        MvPolynomial.C (Polynomial.X ^ η.val.card) *
          D.edgeData.strictOrderEnumerator η.val m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n :=
  ⟨weightedComponentHRV D θ, component_weighted_strict_eq_eval θ,
    weightedComponentHRV_coeff_nonneg D θ, weightedComponentHRV_isWeightedHomogeneous_degree D θ⟩

/-! ### Deprecated names (renamed 2026-10-01) -/

@[deprecated component_strict_eq_elementary (since := "2026-10-01")]
alias component_strict_eq_elementary_by_diagrams := component_strict_eq_elementary
@[deprecated component_weighted_strict_eq_orientation_sum (since := "2026-10-01")]
alias component_weighted_strict_eq_orientation_sum_by_diagrams :=
  component_weighted_strict_eq_orientation_sum
@[deprecated component_weighted_strict_eq_eval (since := "2026-10-01")]
alias component_weighted_strict_eq_eval_by_diagrams := component_weighted_strict_eq_eval
@[deprecated component_weighted_e_positive (since := "2026-10-01")]
alias component_weighted_e_positive_by_diagrams := component_weighted_e_positive

end VerticalStripLLT.Circular

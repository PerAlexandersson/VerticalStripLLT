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
theorem component_strict_eq_elementary_by_diagrams (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) :=
  component_identity_of_forward_components θ m fun _ hforward η =>
    component_strict_eq_elementary_of_forward_by_diagrams η hforward m

/-- Restore the common shifted q-weight, exposing the actual HRV sum. -/
theorem component_weighted_strict_eq_orientation_sum_by_diagrams (θ : Orientation D)
    (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    ∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * evalElementary m η.hrvMonomial := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary_by_diagrams]
  simp only [componentHRV, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun η hη => by rw [card_eq_of_mem_flipComponent hη]

/-- One formal elementary expression represents the weighted component in all
alphabets. -/
theorem component_weighted_strict_eq_eval_by_diagrams (θ : Orientation D) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    evalElementary m (weightedComponentHRV D θ) := by
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary_by_diagrams]
  simp only [weightedComponentHRV, map_mul, evalElementary_C]

/-- Every whole circular component has a homogeneous elementary-positive expansion. -/
theorem component_weighted_e_positive_by_diagrams (θ : Orientation D) :
    ∃ f : EExpansion,
      (∀ m, (∑ η ∈ flipComponent D θ,
        MvPolynomial.C (Polynomial.X ^ η.val.card) *
          D.edgeData.strictOrderEnumerator η.val m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n :=
  ⟨weightedComponentHRV D θ, component_weighted_strict_eq_eval_by_diagrams θ,
    weightedComponentHRV_coeff_nonneg D θ, weightedComponentHRV_isWeightedHomogeneous_degree D θ⟩

end VerticalStripLLT.Circular

import VerticalStripLLT.Components.DiagramProof.Induction.Expansion
import VerticalStripLLT.Components.ComponentPositive

/-!
# The ordinary component theorem by diagrams, and its consequences

For every forward (ordinary, non-circular) decorated diagram, every whole flip
component and every finite alphabet, the strict-coloring enumerator of the
component equals the evaluated sum of the HRV elementary monomials of its states.
Restoring the constant shifted weight gives one homogeneous elementary expression
with nonnegative coefficients.

These declarations use only the diagram route of `DiagramProof`; the earlier
word-functional component theorem is not imported.
-/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators
open DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- **The ordinary component theorem, by diagrams.** -/
theorem component_strict_eq_elementary_of_forward (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) :=
  component_eq_by_diagrams_aux n _ _ D hforward rfl rfl θ m

/-- Restore the common shifted weight: one formal elementary expression represents
the weighted component in every alphabet. -/
theorem component_weighted_strict_eq_eval_of_forward (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    (∑ η ∈ flipComponent D θ,
      MvPolynomial.C (Polynomial.X ^ η.val.card) * D.edgeData.strictOrderEnumerator η.val m) =
    evalElementary m (weightedComponentHRV D θ) := by
  rw [weighted_componentStrictEnumerator,
    component_strict_eq_elementary_of_forward θ hforward]
  simp only [weightedComponentHRV, map_mul, evalElementary_C]

/-- Every whole ordinary component has a homogeneous elementary-positive expansion. -/
theorem component_weighted_e_positive_of_forward (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    ∃ f : EExpansion,
      (∀ m, (∑ η ∈ flipComponent D θ,
        MvPolynomial.C (Polynomial.X ^ η.val.card) *
          D.edgeData.strictOrderEnumerator η.val m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n :=
  ⟨weightedComponentHRV D θ, component_weighted_strict_eq_eval_of_forward θ hforward,
    weightedComponentHRV_coeff_nonneg D θ, weightedComponentHRV_isWeightedHomogeneous_degree D θ⟩

/-! ### Deprecated names (renamed 2026-10-01) -/

@[deprecated component_strict_eq_elementary_of_forward (since := "2026-10-01")]
alias component_strict_eq_elementary_of_forward_by_diagrams :=
  component_strict_eq_elementary_of_forward
@[deprecated component_weighted_strict_eq_eval_of_forward (since := "2026-10-01")]
alias component_weighted_strict_eq_eval_of_forward_by_diagrams :=
  component_weighted_strict_eq_eval_of_forward
@[deprecated component_weighted_e_positive_of_forward (since := "2026-10-01")]
alias component_weighted_e_positive_of_forward_by_diagrams :=
  component_weighted_e_positive_of_forward

end VerticalStripLLT.Circular

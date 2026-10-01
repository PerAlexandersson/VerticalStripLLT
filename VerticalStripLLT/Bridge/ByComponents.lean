import VerticalStripLLT.Bridge.PathDiagram
import VerticalStripLLT.Circular.OrientationSum
import VerticalStripLLT.Components.DiagramProof.Consequences
import VerticalStripLLT.Components.FlipClosedSums
import VerticalStripLLT.QShiftInjective
import VerticalStripLLT.OrientationPositive
import VerticalStripLLT.OrientationDegree

/-!
# The Alexandersson–Sulzgruber expansion from the component theorem by diagrams

For a forward diagram the shifted coloring sum is a sum over states, and the ordinary
component theorem by diagrams identifies it on every whole flip component. With
`SchroderPath.toDiagram` this gives the expansion of [AS22] for every ordinary path.
This uses neither the recursion of [AS22] nor the circular expansion.
-/

namespace VerticalStripLLT

open scoped BigOperators

namespace Circular

open Classical

/-- For a forward diagram, the whole-diagram expansion follows from the component
theorem by diagrams, summed over all flip components. -/
theorem coloringLLT_shifted_eq_eval_of_forward_by_components {n : ℕ} (D : Diagram n)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  rw [Diagram.coloringLLT, EdgeData.xQShift_coloringLLT_eq_orientation_sum]
  have hre : (∑ θ : Orientation D, MvPolynomial.C (Polynomial.X ^ θ.val.card) *
        D.edgeData.strictOrderEnumerator θ.val m) =
      ∑ A ∈ D.edgeData.normalEdges.powerset.filter D.edgeData.Admissible,
        MvPolynomial.C (Polynomial.X ^ A.card) * D.edgeData.strictOrderEnumerator A m := by
    apply Finset.sum_bij (fun θ _ => θ.val)
    · intro θ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr θ.property.1, θ.property.2⟩
    · intro θ _ η _ h
      exact Subtype.ext h
    · intro A hA
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hA
      exact ⟨⟨A, Finset.mem_powerset.mp h1, h2⟩, Finset.mem_univ _, rfl⟩
    · intro θ _
      rfl
  rw [← hre]
  simp only [shiftedOrientationExpansion, map_sum, map_mul, evalElementary_C]
  apply sum_eq_of_flipComponent_sum_eq_of_closed Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _)
  intro θ
  rw [weighted_componentStrictEnumerator, component_strict_eq_elementary_of_forward θ hforward m]
  simp only [componentHRV, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun η hη => by rw [card_eq_of_mem_flipComponent hη]

end Circular

/-- The ordinary shifted expansion, from the component theorem by diagrams. -/
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_components {n : ℕ}
    (P : SchroderPath n) (m : ℕ) :
    xQShift m (coloringLLT P m) = evalElementary m (shiftedOrientationExpansion P) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coloringLLT_size_zero, shiftedOrientationExpansion_size_zero, map_one, map_one]
  · rw [← P.toDiagram_coloringLLT hn, ← P.toDiagram_shiftedOrientationExpansion hn]
    exact Circular.coloringLLT_shifted_eq_eval_of_forward_by_components _
      (P.toDiagram_forward hn) m

/-- The unshifted expansion of [AS22], by the component route. -/
theorem coloringLLT_eq_eval_orientationExpansion_by_components {n : ℕ} (P : SchroderPath n)
    (m : ℕ) : coloringLLT P m = evalElementary m (orientationExpansion P) := by
  apply xQShift_injective m
  rw [coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_components,
    xQShift_evalElementary_orientationExpansion]

/-- Shifted elementary positivity of [AS22], by the component route. -/
theorem coloringLLT_shifted_e_positive_by_components {n : ℕ} (P : SchroderPath n) :
    ∃ f : EExpansion,
      (∀ m, xQShift m (coloringLLT P m) = evalElementary m f) ∧
      (∀ (d : ℕ+ →₀ ℕ) (j : ℕ), 0 ≤ (f.coeff d).coeff j) ∧
      MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val) f n :=
  ⟨shiftedOrientationExpansion P,
    coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_components P,
    shiftedOrientationExpansion_coeff_nonneg P,
    shiftedOrientationExpansion_isWeightedHomogeneous_degree P⟩

end VerticalStripLLT

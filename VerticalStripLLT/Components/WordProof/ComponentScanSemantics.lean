import VerticalStripLLT.Components.WordProof.MountainScanPairing
import VerticalStripLLT.Components.WordProof.ColorProductPairing
import VerticalStripLLT.Circular.HRVEvaluation

/-! The actual component coloring sum as a sum of literal per-state scans. -/

namespace VerticalStripLLT.Components

open Classical
open Circular
open scoped BigOperators TensorProduct

noncomputable section

variable {n : ℕ} {D : Circular.Diagram n}

local instance componentScanTensorRing (K : Type*) [CommRing K] :
    Ring (K ⊗[ℤ] WordAlgebra (Fin n)) := Algebra.TensorProduct.instRing

/-- Include the full-word guard before distributing the component count. -/
theorem cast_componentWordCount_eq_full_sum (K : Type*) [CommRing K]
    (θ : Circular.Orientation D) (w : List (Fin n)) :
    algebraMap ℤ K (componentWordCount D θ w) =
      ∑ η ∈ flipComponent D θ,
        if fullWord w ∧ wordCompatible (D.edgeData.selected η.val) w then (1 : K) else 0 := by
  by_cases hw : fullWord w
  · simp only [hw, true_and]
    exact cast_componentWordCount_eq_sum K θ w hw
  · simp only [componentWordCount_of_not_full θ hw, map_zero, hw, false_and,
      ite_false, Finset.sum_const_zero]

/-- Cauchy pairing reduces ordinary component colorings to literal per-state scans. -/
theorem componentStrictEnumerator_eq_mountainScan_sum
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m =
      ∑ η ∈ flipComponent D θ,
        mountainScan
          (elementaryScalar (List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m))))
          n n (fun w => if fullWord w ∧ wordCompatible (D.edgeData.selected η.val) w
            then 1 else 0) := by
  let xs := List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m))
  have hp := componentScalarEval_cauchyProduct_scan θ hforward xs [] n le_rfl
  have hnil : scalarWord (XPoly m) ([] : List (Fin n)) = 1 := by
    simp [scalarWord, algebraWord_nil, Algebra.TensorProduct.one_def]
  rw [hnil, one_mul, componentScalarEval_cauchyProduct] at hp
  simp only [List.nil_append] at hp
  rw [hp, ← mountainScan_sum]
  apply mountainScan_congr
  intro w
  exact cast_componentWordCount_eq_full_sum (XPoly m) θ w

/-- The scalar weights in the scan are exactly the evaluated elementary HRV monomial. -/
theorem eval_hrvMonomial_eq_elementaryScalar_product (η : Circular.Orientation D) (m : ℕ) :
    evalElementary m η.hrvMonomial =
      ∏ r : Fin n,
        elementaryScalar (List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m)))
          (Finset.univ.filter (fun v => η.hrv v = r)).card := by
  rw [η.evalElementary_hrvMonomial m]
  simp only [elementaryScalar_ofFn_XPoly]

end

end VerticalStripLLT.Components

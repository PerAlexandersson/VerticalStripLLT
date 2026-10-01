import VerticalStripLLT.Components.WordProof.ComponentScanSemantics
import VerticalStripLLT.Components.WordProof.HRVScanExtraction

/-! The ordinary component identity from the actual component word functional. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n}

/-- The ordinary component identity, proved from the actual component word functional. -/
theorem component_strict_eq_elementary_of_forward (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  rw [componentStrictEnumerator_eq_mountainScan_sum θ hforward m]
  simp only [componentHRV, map_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [eval_hrvMonomial_eq_elementaryScalar_product η m]
  let a := elementaryScalar (List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m)))
  have ha0 : a 0 = 1 := elementaryScalar_zero _
  exact η.mountainScan_fullWord_compatible hforward a ha0

end VerticalStripLLT.Circular

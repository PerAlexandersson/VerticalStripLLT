import VerticalStripLLT.ReductionRecursion
import VerticalStripLLT.ColoringRecursion
import VerticalStripLLT.ThirdBounceWeight

namespace VerticalStripLLT

set_option linter.unusedVariables false in
theorem coloringLLT_satisfiesReductionRecursion (m : ℕ) :
    SatisfiesReductionRecursion (MvPolynomial.C Polynomial.X)
      (fun k => MvPolynomial.esymm (Fin m) Q k)
      (fun _ P => coloringLLT P m) := by
  have H := coloringLLT_satisfiesRecursion m
  refine
    { toSatisfiesRecursion := H
      firstBounceOneLeadingEast := ?_ }
  intro n U V W hV h hreturn hgap
  exact coloringLLT_firstBounce_general U (Step.east :: V) W h hreturn hgap m

end VerticalStripLLT

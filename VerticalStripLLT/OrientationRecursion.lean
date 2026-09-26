import VerticalStripLLT.OrientationSecondBounce
import VerticalStripLLT.OrientationFirstBounceSpecializations
import VerticalStripLLT.OrientationSpecializations
import VerticalStripLLT.ColumnBridge
import VerticalStripLLT.ElementaryIndex
import VerticalStripLLT.ReductionRecursion

namespace VerticalStripLLT

set_option linter.unusedVariables false in
theorem orientationExpansion_satisfiesReductionRecursion :
    SatisfiesReductionRecursion (MvPolynomial.C Polynomial.X) elementaryNat
      (fun _ P => orientationExpansion P) := by
  refine
    { toSatisfiesRecursion :=
        { empty := ?_
          column := ?_
          concat := ?_
          unicellular := ?_
          firstBounce := ?_
          secondBounce := ?_ }
      firstBounceOneLeadingEast := ?_
      secondBounceOneLeadingEast := ?_ }
  · simpa using orientationExpansion_empty
  · intro k
    simpa only [elementaryNat_succ] using orientationExpansion_column k
  · intro n k P Q
    exact orientationExpansion_concat P Q
  · intro n U V h
    exact orientationExpansion_unicellular U V h
  · intro n U V W hV h hreturn hgap
    exact orientationExpansion_firstBounce_general U V W h hreturn hgap
  · intro n U V W hV h hreturn hgap
    exact orientationExpansionAt_secondBounce_general U V W h hreturn hgap
      (Polynomial.X - 1)
  · intro n U V W _ h hreturn hgap
    exact orientationExpansion_firstBounce_general U (Step.east :: V) W h hreturn hgap
  · intro n U V W _ h hreturn hgap
    exact orientationExpansionAt_secondBounce_general U (Step.east :: V) W h hreturn hgap
      (Polynomial.X - 1)

end VerticalStripLLT

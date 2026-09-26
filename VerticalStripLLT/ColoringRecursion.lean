import VerticalStripLLT.Recursion
import VerticalStripLLT.EmptyBase
import VerticalStripLLT.ColumnBase
import VerticalStripLLT.ColoringConcat
import VerticalStripLLT.Unicellular
import VerticalStripLLT.FirstBounce
import VerticalStripLLT.SecondBounce

namespace VerticalStripLLT

open SchroderPath
open scoped BigOperators

theorem coloringLLT_satisfiesRecursion (m : ℕ) :
    SatisfiesRecursion (MvPolynomial.C Polynomial.X)
      (fun k => MvPolynomial.esymm (Fin m) Q k)
      (fun _ P => coloringLLT P m) := by
  refine
    { empty := ?_
      column := ?_
      concat := ?_
      unicellular := ?_
      firstBounce := ?_
      secondBounce := ?_ }
  · exact coloringLLT_empty m
  · intro k
    exact coloringLLT_column k m
  · intro n k P Q
    exact coloringLLT_concat P Q m
  · intro n U V h
    simpa [map_sub, map_one] using coloringLLT_unicellular U V h m
  · intro n U V W hV h hreturn hgap
    exact coloringLLT_firstBounce U V W hV h hreturn hgap m
  · intro n U V W hV h hreturn hgap
    exact coloringLLT_secondBounce U V W hV h hreturn hgap m

end VerticalStripLLT

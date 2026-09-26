import VerticalStripLLT.Circular.Diagram
import VerticalStripLLT.Circular.EdgeColoring

/-! The coloring-defined circular LLT polynomial, specialized to finite alphabets. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ}

/-- Each natural circular arc remains a separate directed edge instance. -/
noncomputable def edgeData (D : Diagram n) : EdgeData (Fin n) (Edge D.area) where
  tail := Edge.tail
  head := Edge.head
  strict := D.strict

/-- The direct coloring definition, independent of recursion and HRV. -/
noncomputable def coloringLLT (D : Diagram n) (m : ℕ) : XPoly m :=
  D.edgeData.coloringLLT m

end Diagram

end VerticalStripLLT.Circular

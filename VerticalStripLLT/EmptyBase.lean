import VerticalStripLLT.Coloring

namespace VerticalStripLLT

open SchroderPath

/-- Normalize the size-zero path independently of the manuscript's implicit convention. -/
theorem coloringLLT_empty (m : ℕ) : coloringLLT SchroderPath.empty m = 1 := by
  simp [coloringLLT, coloringWeight, admissible, ascentCount]

end VerticalStripLLT


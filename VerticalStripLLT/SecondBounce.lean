import VerticalStripLLT.SecondBounceGeneral

open scoped BigOperators

namespace VerticalStripLLT

-- Keep the no-east hypothesis in the manuscript-facing interface.
set_option linter.unusedVariables false in
open SchroderPath in
theorem coloringLLT_secondBounce {n : ℕ} (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2)
    (m : ℕ) :
    coloringLLT
      (⟨(U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
        SchroderPath n) m =
      coloringLLT (SchroderPath.secondBounceSuccessor U V W h hgap) m := by
  exact coloringLLT_secondBounce_general U V W h hreturn hgap m

end VerticalStripLLT

import VerticalStripLLT.Circular.OneBounceDNData
import VerticalStripLLT.Circular.SecondBounceRecurrences

/-! Semantic identities for the concrete one-bounce DN target. -/

namespace VerticalStripLLT.Circular.Diagram.OneBounceDNData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.OneBounceDNData t)

theorem coloring_identity (m : ℕ) :
    D.coloringLLT m = B.target.coloringLLT m := by
  exact D.coloringLLT_dnSuccessor B.e B.f B.he B.hf B.hfe B.contact B.sameArea
    B.areaBound B.nonstrict B.rootLength B.rootGap m

theorem shifted_coloring_identity (m : ℕ) :
    xQShift m (D.coloringLLT m) = xQShift m (B.target.coloringLLT m) := by
  exact congrArg (xQShift m) (B.coloring_identity m)

theorem orientation_identity :
    shiftedOrientationExpansion D = shiftedOrientationExpansion B.target := by
  exact D.shiftedOrientationExpansion_dnSuccessor B.e B.f B.he B.hf B.hfe B.contact
    B.sameArea B.areaBound B.nonstrict B.rootLength B.rootGap

theorem expansion_iff_target (m : ℕ) :
    (xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)) ↔
      xQShift m (B.target.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion B.target) := by
  exact D.expansion_iff_secondBounce B.e B.f B.he B.hf B.hfe B.contact B.sameArea
    B.areaBound B.nonstrict B.rootLength B.rootGap m

end VerticalStripLLT.Circular.Diagram.OneBounceDNData

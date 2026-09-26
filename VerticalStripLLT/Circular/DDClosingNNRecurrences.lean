import VerticalStripLLT.Circular.DDDeletedClosingNN
import VerticalStripLLT.Circular.OneBounceDNRecurrences

/-! Actual corner cancellation for the two NN child targets. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem coloring_closing_nn (ht : D.EligibleDE t)
    (hr : B.resolved.EligibleDE (D.boundary t + 1))
    (hc : B.deleted.EligibleDE (D.boundary t)) (m : ℕ) :
    xQShift m ((B.resolved.shortenEligible (D.boundary t + 1) hr).coloringLLT m) -
      xQShift m ((B.deletedShortened hc).coloringLLT m) =
        MvPolynomial.C Polynomial.X * xQShift m ((D.shortenEligible t ht).coloringLLT m) := by
  obtain ⟨e, he, hh, hu⟩ := B.resolved_shorten_eq_unstrict ht hr
  rw [hu, (B.closingDN ht hc).shifted_coloring_identity,
    B.closingDN_target_eq_deleteCorner ht hc e he hh,
    (D.shortenEligible t ht).xQShift_coloringLLT_unstrict_corner e he m]
  ring

theorem orientation_closing_nn (ht : D.EligibleDE t)
    (hr : B.resolved.EligibleDE (D.boundary t + 1))
    (hc : B.deleted.EligibleDE (D.boundary t)) :
    shiftedOrientationExpansion (B.resolved.shortenEligible (D.boundary t + 1) hr) -
      shiftedOrientationExpansion (B.deletedShortened hc) =
        MvPolynomial.C Polynomial.X * shiftedOrientationExpansion (D.shortenEligible t ht) := by
  obtain ⟨e, he, hh, hu⟩ := B.resolved_shorten_eq_unstrict ht hr
  rw [hu, (B.closingDN ht hc).orientation_identity,
    B.closingDN_target_eq_deleteCorner ht hc e he hh,
    (D.shortenEligible t ht).shiftedOrientationExpansion_unstrict_corner e he]
  ring

end VerticalStripLLT.Circular.Diagram.DDLocalData

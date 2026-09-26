import VerticalStripLLT.Circular.OneBounceNN
import VerticalStripLLT.Circular.DDClosingNNRecurrences
import VerticalStripLLT.Circular.DDResolvedChild
import VerticalStripLLT.Circular.DDDeletedChild
import VerticalStripLLT.Circular.DDLocalRealization
import VerticalStripLLT.Circular.DDRecurrences

/-! Eliminate DD contacts using the direct NN/DN and corner relations.
The contact count is auxiliary; the final NN target drops one full square. -/

namespace VerticalStripLLT.Circular.Diagram

/-- The two actual NN identities, proved together by local DD elimination. -/
theorem shifted_nn_of_counted {n : ℕ} (D : Diagram n) {t x : ℤ} {k : ℕ}
    (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x k) (hx : ¬ D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    (∀ m : ℕ, xQShift m (D.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m ((D.shortenEligible t ht).coloringLLT m)) ∧
    shiftedOrientationExpansion D = MvPolynomial.C (Polynomial.X + 1) *
      shiftedOrientationExpansion (D.shortenEligible t ht) := by
  induction k generalizing D t x with
  | zero =>
    exact ⟨D.shifted_coloringLLT_oneBounce_NN ht h hx hx1,
      D.shiftedOrientationExpansion_oneBounce_NN ht h hx hx1⟩
  | succ k ih =>
    obtain ⟨B⟩ := D.exists_ddLocalData ht h
    obtain ⟨hr, hbr, hxr, hx1r, har⟩ := B.resolved_dd_child ht ha h hx1
    obtain ⟨hc, hbc, hxc, hx1c, hac⟩ := D.delete_dd_child ht ha h B.g B.hg B.gh
    obtain ⟨cr, er⟩ := ih B.resolved hr har hbr (fun hz => hx (hxr.mp hz))
      (fun hz => hx1 (hx1r.mp hz))
    obtain ⟨cc, ec⟩ := ih B.deleted hc hac hbc (fun hz => hx (hxc.mp hz))
      (fun hz => hx1 (hx1c.mp hz))
    constructor
    · intro m
      have hq : (MvPolynomial.C Polynomial.X : XPoly m) ≠ 0 :=
        (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero
      apply mul_left_cancel₀ hq
      rw [B.coloring_resolution m, cr m, cc m, ← mul_sub]
      change _ * (xQShift m
        ((B.resolved.shortenEligible (D.boundary t + 1) hr).coloringLLT m) -
        xQShift m ((B.deletedShortened hc).coloringLLT m)) = _
      rw [B.coloring_closing_nn ht hr hc m]
      ring
    · have hq : (MvPolynomial.C Polynomial.X : EExpansion) ≠ 0 :=
        (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero
      apply mul_left_cancel₀ hq
      rw [B.orientation_resolution, er, ec, ← mul_sub]
      change _ * (shiftedOrientationExpansion
        (B.resolved.shortenEligible (D.boundary t + 1) hr) -
        shiftedOrientationExpansion (B.deletedShortened hc)) = _
      rw [B.orientation_closing_nn ht hr hc]
      ring

/-- Complete NN elimination discharges the branch using a smaller-area target. -/
theorem expansion_of_nn {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounce D t x) (hx : ¬ D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨k, hk⟩ := D.reverseBounce_to_counted h
  obtain ⟨hc, he⟩ := D.shifted_nn_of_counted ht ha hk hx hx1
  have hi := ih (D.shortenEligible t ht) (by have := D.shortenEligible_doubledArea t ht; lia)
  rw [hc m, he, map_mul, evalElementary_C, hi]

end VerticalStripLLT.Circular.Diagram

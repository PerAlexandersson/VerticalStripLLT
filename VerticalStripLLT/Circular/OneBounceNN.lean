import VerticalStripLLT.Circular.EligibleShorten
import VerticalStripLLT.Circular.FirstBounceRecurrences
import VerticalStripLLT.Circular.FirstBounceOrientation
import VerticalStripLLT.Circular.CountedBounce
import VerticalStripLLT.Circular.DNRealization

/-! The canonical one-bounce NN identities at an eligible row. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

theorem coloringLLT_oneBounce_NN {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X *
      (D.shortenEligible t ht).coloringLLT m := by
  obtain ⟨hx0, hgap, hnot⟩ := (ReverseBounceN.zero_iff D).mp h
  subst hx0
  let e := D.eligibleEdge t ht
  have he : e ∈ D.strict := D.eligibleEdge_mem t ht
  have eh : e.head = D.residue t := D.eligibleEdge_head t ht
  have hres : D.residue (e.tail.val : ℤ) = D.residue (D.boundary t) :=
    (Orientation.residue_intCast_eq e.tail).trans
      (D.strictEdge_tail_of_lift he eh)
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period hres
  have hsame0 : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t) := by
    unfold eastGap at hgap
    rw [ite_eq_right hx] at hgap
    lia
  have hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ) := by
    rw [hk, show D.boundary t + (n : ℤ) * k + 1 =
      D.boundary t + 1 + (n : ℤ) * k by ring,
      D.boundary_add_period, D.boundary_add_period]
    rw [hsame0]
  have hleft : ¬ D.strictAt (e.tail.val : ℤ) := by
    rw [hk, D.strictAt_add_period]
    exact hx
  have hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1) := by
    rw [hk, show D.boundary t + (n : ℤ) * k + 1 =
      D.boundary t + 1 + (n : ℤ) * k by ring, D.strictAt_add_period]
    exact hx1
  change D.coloringLLT m = MvPolynomial.C Polynomial.X *
    (D.shortenStrict e he (D.eligibleEdge_length t ht) (D.eligibleEdge_gap t ht)).coloringLLT m
  exact D.coloringLLT_shortenStrict_NN e he (D.eligibleEdge_length t ht)
    (D.eligibleEdge_gap t ht) hsame hleft hright m

theorem shifted_coloringLLT_oneBounce_NN {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) (m : ℕ) :
    xQShift m (D.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m ((D.shortenEligible t ht).coloringLLT m) := by
  rw [D.coloringLLT_oneBounce_NN ht h hx hx1 m, map_mul]
  congr 1
  simpa using xQShift_C_X_pow' m 1

theorem shiftedOrientationExpansion_oneBounce_NN {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    shiftedOrientationExpansion D = MvPolynomial.C (Polynomial.X + 1) *
      shiftedOrientationExpansion (D.shortenEligible t ht) := by
  obtain ⟨hx0, hgap, hnot⟩ := (ReverseBounceN.zero_iff D).mp h
  subst hx0
  let e := D.eligibleEdge t ht
  have he : e ∈ D.strict := D.eligibleEdge_mem t ht
  have eh : e.head = D.residue t := D.eligibleEdge_head t ht
  have hres : D.residue (e.tail.val : ℤ) = D.residue (D.boundary t) :=
    (Orientation.residue_intCast_eq e.tail).trans
      (D.strictEdge_tail_of_lift he eh)
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period hres
  have hsame0 : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t) := by
    unfold eastGap at hgap
    rw [ite_eq_right hx] at hgap
    lia
  have hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ) := by
    rw [hk, show D.boundary t + (n : ℤ) * k + 1 =
      D.boundary t + 1 + (n : ℤ) * k by ring,
      D.boundary_add_period, D.boundary_add_period]
    rw [hsame0]
  have hleft : ¬ D.strictAt (e.tail.val : ℤ) := by
    rw [hk, D.strictAt_add_period]
    exact hx
  have hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1) := by
    rw [hk, show D.boundary t + (n : ℤ) * k + 1 =
      D.boundary t + 1 + (n : ℤ) * k by ring, D.strictAt_add_period]
    exact hx1
  change shiftedOrientationExpansion D = MvPolynomial.C (Polynomial.X + 1) *
    shiftedOrientationExpansion
      (D.shortenStrict e he (D.eligibleEdge_length t ht) (D.eligibleEdge_gap t ht))
  exact D.shiftedOrientationExpansion_shortenStrict_NN e he
    (D.eligibleEdge_length t ht) (D.eligibleEdge_gap t ht) hsame hleft hright

end VerticalStripLLT.Circular.Diagram

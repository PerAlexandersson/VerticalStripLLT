import VerticalStripLLT.Circular.FirstBounceOrientation
import VerticalStripLLT.Circular.FirstBounceGeometry

/-! Coloring and HRV NN recurrences in the same geometric coordinates. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem coloringLLT_shortenStrict_NN
    (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
    (hleft : ¬ D.strictAt (e.tail.val : ℤ))
    (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1)) (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X *
      (D.shortenStrict e he hlen hgap).coloringLLT m := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period
    ((D.strictEdge_tail_boundary he).symm.trans (Orientation.residue_intCast_eq e.tail).symm)
  apply D.coloringLLT_firstBounce_geometry he hlen hgap
  · rw [hk, show (e.tail.val : ℤ) + n * k + 1 = (e.tail.val : ℤ) + 1 + n * k by ring,
      D.boundary_add_period, D.boundary_add_period, hsame]
  · rw [hk, D.strictAt_add_period]
    exact hleft
  · rw [hk, show (e.tail.val : ℤ) + n * k + 1 = (e.tail.val : ℤ) + 1 + n * k by ring,
      D.strictAt_add_period]
    exact hright

theorem xQShift_coloringLLT_shortenStrict_NN
    (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
    (hleft : ¬ D.strictAt (e.tail.val : ℤ))
    (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1)) (m : ℕ) :
    xQShift m (D.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m ((D.shortenStrict e he hlen hgap).coloringLLT m) := by
  rw [D.coloringLLT_shortenStrict_NN e he hlen hgap hsame hleft hright m, map_mul]
  congr 1
  simpa using xQShift_C_X_pow' m 1

/-- An induction step, using independently proved recurrences for both actual models. -/
theorem expansion_of_firstBounce_NN
    (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
    (hleft : ¬ D.strictAt (e.tail.val : ℤ))
    (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1)) (m : ℕ)
    (ih : xQShift m ((D.shortenStrict e he hlen hgap).coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion (D.shortenStrict e he hlen hgap))) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  rw [D.xQShift_coloringLLT_shortenStrict_NN e he hlen hgap hsame hleft hright m,
    D.shiftedOrientationExpansion_shortenStrict_NN e he hlen hgap hsame hleft hright,
    map_mul, evalElementary_C, ih]

end Diagram
end VerticalStripLLT.Circular

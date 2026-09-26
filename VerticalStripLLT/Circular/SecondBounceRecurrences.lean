import VerticalStripLLT.Circular.SecondBounceOrientation
import VerticalStripLLT.Circular.SecondBounceGeometry

/-! The direct DN move preserves the actual circular expansion statement. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

/-- Both sides of the semantic bridge satisfy the same independently proved DN identity. -/
theorem expansion_iff_secondBounce
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
    (hcontact : f.tail = e.head)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) (m : ℕ) :
    (xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D)) ↔
      xQShift m ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion
          (D.dnSuccessor e f he hf hne heq hb hns hlen hgap)) := by
  rw [D.coloringLLT_dnSuccessor e f he hf hne hcontact heq hb hns hlen hgap m,
    D.shiftedOrientationExpansion_dnSuccessor e f he hf hne hcontact heq hb hns hlen hgap]

end VerticalStripLLT.Circular.Diagram

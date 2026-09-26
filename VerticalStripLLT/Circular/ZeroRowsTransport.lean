import VerticalStripLLT.Circular.DNTarget
import VerticalStripLLT.Circular.DDResolvedRows

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} {D : Diagram n}

/-- A direct DN move preserves exactly the zero rows of its source diagram. -/
theorem dnSuccessor_area_eq_zero_iff (e f : Edge D.area) (he : e ∈ D.strict)
    (hf : f ∈ D.strict) (hne : f ≠ e)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)
    (v : Fin n) :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).area.area v = 0 ↔
      D.area.area v = 0 := by
  rw [D.dnSuccessor_area e f he hf hne heq hb hns hlen hgap]
  have hepos : 0 < D.area.area e.head :=
    lt_of_lt_of_le e.length_pos e.length_le_area
  have hf2 : 2 ≤ D.area.area f.head := hlen.trans f.length_le_area
  have hnextf : D.area.next e.head ≠ f.head := by
    intro h
    exact hns f hf h.symm
  by_cases hv : v = D.area.next e.head
  · subst hv
    rw [Function.update_of_ne hnextf, Function.update_self]
    lia
  by_cases hvf : v = f.head
  · subst hvf
    rw [Function.update_self]
    lia
  · rw [Function.update_of_ne hvf, Function.update_of_ne hv]

/-- The concrete resolved DD child also preserves the source zero rows. -/
theorem DDLocalData.resolved_area_eq_zero_iff
    {t : ℤ} (B : D.DDLocalData t) (v : Fin n) :
    B.resolved.area.area v = 0 ↔ D.area.area v = 0 := by
  have h := dnSuccessor_area_eq_zero_iff (D := D.unstrict B.g B.hg) B.e B.f
    (Finset.mem_erase.mpr ⟨B.heg, B.he⟩)
    (Finset.mem_erase.mpr ⟨B.hfg, B.hf⟩) B.hfe B.sameArea B.areaBound
    (D.dd_unstrict_no_head B.e B.g B.hg B.head) B.rootLength B.rootGap v
  simpa only [DDLocalData.resolved, ddResolved, unstrict] using h

end VerticalStripLLT.Circular.Diagram

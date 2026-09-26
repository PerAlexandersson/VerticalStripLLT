import VerticalStripLLT.Circular.UnstrictCorner
import VerticalStripLLT.Circular.SecondBounceRecurrences

/-! The first DD elimination for the independently defined coloring and HRV models. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)
  (e f g : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hg : g ∈ D.strict)
  (hfe : f ≠ e) (heg : e ≠ g) (hfg : f ≠ g)
  (hhead : g.head = D.area.next e.head)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

include hhead in
theorem dd_unstrict_no_head :
    ∀ a ∈ (D.unstrict g hg).strict, a.head ≠ D.area.next e.head := by
  intro a ha hai
  exact (Finset.mem_erase.mp ha).1
    (D.strict_edge_eq_of_head_eq (Finset.mem_erase.mp ha).2 hg (hai.trans hhead.symm))

/-- Unstrict the last parallel contact, then perform the direct DN move. -/
noncomputable def ddResolved : Diagram n :=
  (D.unstrict g hg).dnSuccessor e f
    (Finset.mem_erase.mpr ⟨heg, he⟩) (Finset.mem_erase.mpr ⟨hfg, hf⟩)
    hfe heq hb (D.dd_unstrict_no_head e g hg hhead) hlen hgap

theorem xQShift_ddCorner_resolution (hcontact : f.tail = e.head) (m : ℕ) :
    MvPolynomial.C Polynomial.X * xQShift m (D.coloringLLT m) =
      xQShift m ((D.ddResolved e f g he hf hg hfe heg hfg hhead heq hb hlen hgap).coloringLLT m) -
        xQShift m ((D.deleteCorner g (D.strict_corner g hg)).coloringLLT m) := by
  have hd := (D.unstrict g hg).xQShift_coloringLLT_dnSuccessor e f
    (Finset.mem_erase.mpr ⟨heg, he⟩) (Finset.mem_erase.mpr ⟨hfg, hf⟩)
    hfe hcontact heq hb (D.dd_unstrict_no_head e g hg hhead) hlen hgap m
  change xQShift m ((D.unstrict g hg).coloringLLT m) =
    xQShift m ((D.ddResolved e f g he hf hg hfe heg hfg hhead heq hb hlen hgap).coloringLLT m)
    at hd
  rw [← hd, D.xQShift_coloringLLT_unstrict_corner g hg m, add_sub_cancel_right]

theorem shiftedOrientationExpansion_ddCorner_resolution (hcontact : f.tail = e.head) :
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion D =
      shiftedOrientationExpansion
        (D.ddResolved e f g he hf hg hfe heg hfg hhead heq hb hlen hgap) -
        shiftedOrientationExpansion (D.deleteCorner g (D.strict_corner g hg)) := by
  have hd := (D.unstrict g hg).shiftedOrientationExpansion_dnSuccessor e f
    (Finset.mem_erase.mpr ⟨heg, he⟩) (Finset.mem_erase.mpr ⟨hfg, hf⟩)
    hfe hcontact heq hb (D.dd_unstrict_no_head e g hg hhead) hlen hgap
  change shiftedOrientationExpansion (D.unstrict g hg) =
    shiftedOrientationExpansion
      (D.ddResolved e f g he hf hg hfe heg hfg hhead heq hb hlen hgap) at hd
  rw [← hd, D.shiftedOrientationExpansion_unstrict_corner g hg, add_sub_cancel_right]

end VerticalStripLLT.Circular.Diagram

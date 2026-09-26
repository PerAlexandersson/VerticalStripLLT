import VerticalStripLLT.Circular.CornerDeleteOrientation
import VerticalStripLLT.Circular.BoundaryRow
import VerticalStripLLT.Circular.StrictEdgeInjectivity

/-! Removing one strict corner, with strictification as its inverse. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped BigOperators Classical

variable {n : ℕ} (D : Diagram n)

noncomputable def unstrict (e : Edge D.area) (_he : e ∈ D.strict) : Diagram n where
  area := D.area
  strict := D.strict.erase e
  strict_corner := by
    intro f hf
    exact D.strict_corner f (Finset.mem_erase.mp hf).2

theorem unstrict_area (e : Edge D.area) (he : e ∈ D.strict) :
    (D.unstrict e he).area = D.area := rfl

theorem unstrict_strictify (e : Edge D.area) (he : e ∈ D.strict) :
    (D.unstrict e he).strictify e (D.strict_corner e he) = D := by
  cases D
  simp only [unstrict, strictify, Finset.insert_erase he]

theorem unstrict_deleteCorner (e : Edge D.area) (he : e ∈ D.strict)
    (hc : IsCorner e) :
    (D.unstrict e he).deleteCorner e hc = D.deleteCorner e hc := by
  have hs : ((D.unstrict e he).deleteCorner e hc).strict =
      (D.deleteCorner e hc).strict := by
    ext f
    simp only [deleteCorner, unstrict, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    exact ⟨fun h => h.2, fun h => ⟨D.cornerIncl_ne e hc f, h⟩⟩
  unfold deleteCorner
  congr 1

theorem unstrict_residue (e : Edge D.area) (he : e ∈ D.strict) (z : ℤ) :
    (D.unstrict e he).residue z = D.residue z := rfl

theorem unstrict_boundary (e : Edge D.area) (he : e ∈ D.strict) (z : ℤ) :
    (D.unstrict e he).boundary z = D.boundary z := rfl

theorem unstrict_strictAt_iff (e : Edge D.area) (he : e ∈ D.strict) (z : ℤ) :
    (D.unstrict e he).strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ e.head := by
  constructor
  · rintro ⟨f, hf, hhead⟩
    refine ⟨⟨f, (Finset.mem_erase.mp hf).2, hhead⟩, ?_⟩
    intro hres
    apply (Finset.mem_erase.mp hf).1
    apply D.strict_edge_eq_of_head_eq (Finset.mem_erase.mp hf).2 he
    exact hhead.trans hres
  · rintro ⟨⟨f, hf, hhead⟩, hne⟩
    refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hhead⟩
    intro hfe
    apply hne
    rw [← hhead, hfe]

theorem xQShift_coloringLLT_unstrict_corner (e : Edge D.area) (he : e ∈ D.strict)
    (m : ℕ) :
    xQShift m ((D.unstrict e he).coloringLLT m) =
      MvPolynomial.C Polynomial.X * xQShift m (D.coloringLLT m) +
        xQShift m ((D.deleteCorner e (D.strict_corner e he)).coloringLLT m) := by
  have hcorner := (D.unstrict e he).xQShift_coloringLLT_corner e (D.strict_corner e he)
    (by simp [unstrict]) m
  rw [D.unstrict_strictify e he,
    D.unstrict_deleteCorner e he (D.strict_corner e he)] at hcorner
  exact hcorner

theorem shiftedOrientationExpansion_unstrict_corner (e : Edge D.area)
    (he : e ∈ D.strict) :
    shiftedOrientationExpansion (D.unstrict e he) =
      MvPolynomial.C Polynomial.X * shiftedOrientationExpansion D +
        shiftedOrientationExpansion (D.deleteCorner e (D.strict_corner e he)) := by
  have hcorner := (D.unstrict e he).shiftedOrientationExpansion_corner e (D.strict_corner e he)
    (by simp [unstrict, he])
  rw [D.unstrict_strictify e he,
    D.unstrict_deleteCorner e he (D.strict_corner e he)] at hcorner
  exact hcorner

end Diagram
end VerticalStripLLT.Circular

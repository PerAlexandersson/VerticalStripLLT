import VerticalStripLLT.Circular.DDCornerResolution
import VerticalStripLLT.Circular.CountedBounce
import VerticalStripLLT.Circular.DNRealization

/-! Geometric data for resolving the last DD contact of an actual bounce. -/

namespace VerticalStripLLT.Circular.Diagram

/-- All data are concrete edges and geometry; no polynomial identity is a field. -/
structure DDLocalData {n : ℕ} (D : Diagram n) (t : ℤ) where
  e : Edge D.area
  f : Edge D.area
  g : Edge D.area
  he : e ∈ D.strict
  hf : f ∈ D.strict
  hg : g ∈ D.strict
  eh : e.head = D.residue (D.boundary t)
  fh : f.head = D.residue t
  gh : g.head = D.residue (D.boundary t + 1)
  hfe : f ≠ e
  heg : e ≠ g
  hfg : f ≠ g
  contact : f.tail = e.head
  head : g.head = D.area.next e.head
  sameArea : D.area.area (D.area.next e.head) = D.area.area e.head
  areaBound : D.area.area e.head + 1 < n
  rootLength : 2 ≤ f.length.val
  rootGap : D.area.area (D.area.next f.head) < D.area.area f.head

namespace DDLocalData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

noncomputable def resolved : Diagram n :=
  D.ddResolved B.e B.f B.g B.he B.hf B.hg B.hfe B.heg B.hfg B.head
    B.sameArea B.areaBound B.rootLength B.rootGap

noncomputable def deleted : Diagram n := D.deleteCorner B.g (D.strict_corner B.g B.hg)

theorem coloring_resolution (m : ℕ) :
    MvPolynomial.C Polynomial.X * xQShift m (D.coloringLLT m) =
      xQShift m (B.resolved.coloringLLT m) - xQShift m (B.deleted.coloringLLT m) :=
  D.xQShift_ddCorner_resolution B.e B.f B.g B.he B.hf B.hg B.hfe B.heg B.hfg
    B.head B.sameArea B.areaBound B.rootLength B.rootGap B.contact m

theorem orientation_resolution :
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion D =
      shiftedOrientationExpansion B.resolved - shiftedOrientationExpansion B.deleted :=
  D.shiftedOrientationExpansion_ddCorner_resolution B.e B.f B.g B.he B.hf B.hg
    B.hfe B.heg B.hfg B.head B.sameArea B.areaBound B.rootLength B.rootGap B.contact

end DDLocalData
end VerticalStripLLT.Circular.Diagram

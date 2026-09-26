import VerticalStripLLT.Circular.DNRealization
import VerticalStripLLT.Circular.DNStrictRows
import VerticalStripLLT.Circular.CountedBounce

/-! Concrete data and the DN target for a single eligible bounce. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

structure OneBounceDNData {n : ℕ} (D : Diagram n) (t : ℤ) where
  e : Edge D.area
  f : Edge D.area
  he : e ∈ D.strict
  hf : f ∈ D.strict
  eh : e.head = D.residue (D.boundary t)
  fh : f.head = D.residue t
  hfe : f ≠ e
  contact : f.tail = e.head
  sameArea : D.area.area (D.area.next e.head) = D.area.area e.head
  areaBound : D.area.area e.head + 1 < n
  nonstrict : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head
  rootLength : 2 ≤ f.length.val
  rootGap : D.area.area (D.area.next f.head) < D.area.area f.head

namespace OneBounceDNData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.OneBounceDNData t)

noncomputable def target : Diagram n :=
  D.dnSuccessor B.e B.f B.he B.hf B.hfe B.sameArea B.areaBound B.nonstrict
    B.rootLength B.rootGap

theorem target_area : B.target.area.area =
    Function.update (Function.update D.area.area (D.area.next B.e.head)
      (D.area.area B.e.head + 1)) B.f.head (D.area.area B.f.head - 1) := by
  exact D.dnSuccessor_area B.e B.f B.he B.hf B.hfe B.sameArea B.areaBound
    B.nonstrict B.rootLength B.rootGap

theorem target_strictAt_iff (z : ℤ) : B.target.strictAt z ↔
    (D.strictAt z ∧ D.residue z ≠ B.e.head) ∨
      D.residue z = D.area.next B.e.head := by
  exact D.dnSuccessor_strictAt_iff B.e B.f B.he B.hf B.hfe B.sameArea
    B.areaBound B.nonstrict B.rootLength B.rootGap z

end OneBounceDNData

theorem exists_oneBounceDNData {n : ℕ} {D : Diagram n} {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    Nonempty (D.OneBounceDNData t) := by
  obtain ⟨hx0, hgap, hnot⟩ := (ReverseBounceN.zero_iff D).mp h
  subst hx0
  obtain ⟨e, he, eh⟩ := hx
  obtain ⟨f, hf, fh⟩ := ht.1
  have hcontact : f.tail = e.head := (D.strictEdge_tail_of_lift hf fh).trans eh.symm
  have hfe : f ≠ e := by
    intro h
    exact f.tail_ne_head (hcontact.trans (congrArg Edge.head h).symm)
  have heq : D.area.area (D.area.next e.head) = D.area.area e.head := by
    rw [eh]
    exact D.strict_zero_gap_area_eq ⟨e, he, eh⟩ hgap
  have hb : D.area.area e.head + 1 < n := by
    by_contra hh
    have hbound := D.area.bound e.head
    have hfull : (D.area.area (D.residue (D.boundary t)) : ℤ) + 1 = n := by
      rw [← eh]
      lia
    have hbb : D.boundary (D.boundary t) = D.boundary t + 1 + (n : ℤ) * (-1) := by
      rw [boundary]
      lia
    have hstep := D.selected_of_strictAt (show D.strictAt (D.boundary t) from ⟨e, he, eh⟩)
    rw [hbb, D.residue_add_period] at hstep
    exact ht.parallel_end_free D _ hstep
  have hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head := by
    intro g hg hhead
    apply hx1
    refine ⟨g, hg, ?_⟩
    rw [hhead, eh, D.residue_succ]
  have hlen : 2 ≤ f.length.val := by
    rw [(D.strict_corner f hf).1, fh]
    exact ht.2.1
  have hgap' : D.area.area (D.area.next f.head) < D.area.area f.head := by
    have hh := ht.boundary_gap D
    simp only [boundary, D.residue_succ, ← fh] at hh
    lia
  exact ⟨{
    e := e
    f := f
    he := he
    hf := hf
    eh := eh
    fh := fh
    hfe := hfe
    contact := hcontact
    sameArea := heq
    areaBound := hb
    nonstrict := hns
    rootLength := hlen
    rootGap := hgap'
  }⟩

end VerticalStripLLT.Circular.Diagram

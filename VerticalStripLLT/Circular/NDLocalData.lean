import VerticalStripLLT.Circular.DDLocalRealization
import VerticalStripLLT.Circular.LowerStrict
import VerticalStripLLT.Circular.ShortenStrictMeasure

/-! Concrete geometry of a single ND contact, allowing circular winding.
No polynomial identities or strict acyclicity are assumed. -/

namespace VerticalStripLLT.Circular.Diagram

structure NDLocalData {n : ℕ} (D : Diagram n) (t : ℤ) where
  f : Edge D.area
  g : Edge D.area
  hf : f ∈ D.strict
  hg : g ∈ D.strict
  fh : f.head = D.residue t
  gh : g.head = D.residue (D.boundary t + 1)
  ft : f.tail = D.residue (D.boundary t)
  head_ne : f.head ≠ g.head
  nonstrict : ¬ D.strictAt (D.boundary t)
  sameBoundary : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t)
  areaEq : D.area.area g.head = D.area.area (D.residue (D.boundary t)) + 1
  areaPos : 1 ≤ D.area.area (D.residue (D.boundary t))
  rootLength : 2 ≤ f.length.val
  rootGap : D.area.area (D.area.next f.head) < D.area.area f.head

variable {n : ℕ} (D : Diagram n)

theorem exists_ndLocalData {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1)) :
    Nonempty (D.NDLocalData t) := by
  obtain ⟨rfl, hgap, _⟩ := (ReverseBounceN.zero_iff D).mp h
  obtain ⟨f, hf, fh⟩ := ht.1
  obtain ⟨g, hg, gh⟩ := hx1
  have hft := D.strictEdge_tail_of_lift hf fh
  have hlen : 2 ≤ f.length.val := by
    rw [(D.strict_corner f hf).1, fh]
    exact ht.2.1
  have hne : f.head ≠ g.head := by
    intro heq
    have hh := fh.symm.trans (heq.trans gh)
    have hb := D.area.bound (D.residue t)
    have hl := ht.2.1
    have hh' := D.eq_of_residue_eq_of_bounds hh
      (by unfold boundary; lia) (by unfold boundary; lia)
    unfold boundary at hh'
    lia
  have hsame : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t) := by
    unfold eastGap at hgap
    rw [ite_eq_right hx] at hgap
    lia
  have heq : D.area.area g.head = D.area.area (D.residue (D.boundary t)) + 1 := by
    rw [gh]
    change D.boundary t + 1 - (D.area.area (D.residue (D.boundary t + 1)) : ℤ) =
      D.boundary t - (D.area.area (D.residue (D.boundary t)) : ℤ) at hsame
    lia
  have hpos : 1 ≤ D.area.area (D.residue (D.boundary t)) := by
    by_contra hh
    have hz : D.area.area (D.residue (D.boundary t)) = 0 := by lia
    have hb : D.boundary (D.boundary t) = D.boundary t := by
      rw [boundary, hz, Nat.cast_zero, sub_zero]
    have hgt : g.tail = D.residue (D.boundary t) := by
      rw [D.strictEdge_tail_of_lift hg gh, hsame, hb]
    have hfg := D.strict_edge_eq_of_tail_eq hf hg (hft.trans hgt.symm)
    exact hne (congrArg Edge.head hfg)
  have hr : D.area.area (D.area.next f.head) < D.area.area f.head := by
    have hh := ht.boundary_gap D
    simp only [boundary, D.residue_succ, ← fh] at hh
    lia
  exact ⟨⟨f, g, hf, hg, fh, gh, hft, hne, hx, hsame, heq, hpos, hlen, hr⟩⟩

namespace NDLocalData

variable {D} {t : ℤ} (B : D.NDLocalData t)

theorem upper_head : B.g.head = D.area.next (D.residue (D.boundary t)) := by
  rw [B.gh, D.residue_succ]

noncomputable def lowered : Diagram n :=
  D.lowerStrict (D.residue (D.boundary t)) B.g B.hg B.upper_head B.areaEq B.areaPos

noncomputable def shortened : Diagram n :=
  D.shortenStrict B.f B.hf B.rootLength B.rootGap

theorem shortened_doubledArea : B.shortened.doubledArea + 2 = D.doubledArea :=
  D.shortenStrict_doubledArea B.f B.hf B.rootLength B.rootGap

end NDLocalData
end VerticalStripLLT.Circular.Diagram

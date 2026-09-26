import VerticalStripLLT.Circular.HRVPotential
import VerticalStripLLT.Circular.NaturalPairSwap
import VerticalStripLLT.Circular.StrictEdgeInjectivity

/-! Adjacency across a strict corner, including edges crossing any chosen cut. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

/-- A strict corner is the longest natural edge leaving its tail. -/
theorem length_le_of_strict_same_tail {e f : Edge D.area}
    (he : e ∈ D.strict) (ht : f.tail = e.tail) : f.length.val ≤ e.length.val := by
  let u : ℤ := e.tail.val
  let w : ℤ := u + e.length.val
  let z : ℤ := u + f.length.val
  have hu : D.residue u = e.tail := Orientation.residue_intCast_eq e.tail
  have hw : D.residue w = e.head := D.residue_add_length e u hu
  have hz : D.residue z = f.head := D.residue_add_length f u (hu.trans ht.symm)
  have hbw : D.boundary w = u := by
    rw [boundary, hw, ← (D.strict_corner e he).1]
    dsimp only [w]
    ring
  have hsw : D.strictAt w := ⟨e, he, hw.symm⟩
  have hbf := (D.boundaryNaturalLift_of_edge hz.symm
    (show (f.length.val : ℤ) = z - u by dsimp only [z]; ring)).1
  by_contra hlt
  have hlt' : (e.length.val : ℤ) < f.length.val := by
    exact_mod_cast (lt_of_not_ge hlt)
  have hwz : w + 1 ≤ z := by dsimp only [w, z]; lia
  have hmono := D.boundary_monotone hwz
  have hstep := D.strictAt_boundary_lt hsw
  rw [hbw] at hstep
  lia

/-- The two natural adjacencies across a strict corner are equivalent. -/
theorem naturalPairs_across_strict_corner_iff {e : Edge D.area}
    (he : e ∈ D.strict) (v : Fin n) (hvt : v ≠ e.tail) (hvh : v ≠ e.head) :
    (e.tail, v) ∈ D.naturalPairs ↔ (v, e.head) ∈ D.naturalPairs := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (D.mem_naturalPairs_iff _).mp h
    obtain ⟨hft, hfh⟩ := Prod.mk.inj hf
    let u : ℤ := e.tail.val
    let w : ℤ := u + e.length.val
    let z : ℤ := u + f.length.val
    have hu : D.residue u = e.tail := Orientation.residue_intCast_eq e.tail
    have hw : D.residue w = e.head := D.residue_add_length e u hu
    have hz : D.residue z = v :=
      (D.residue_add_length f u (hu.trans hft.symm)).trans hfh
    have hlen := D.length_le_of_strict_same_tail he hft
    have hne : f.length.val ≠ e.length.val := by
      intro hfe
      have hzw : z = w := by dsimp only [z, w]; rw [hfe]
      exact hvh (hz.symm.trans ((congrArg D.residue hzw).trans hw))
    have hlt : (f.length.val : ℤ) < e.length.val := by
      exact_mod_cast (lt_of_le_of_ne hlen hne)
    have hbw : D.boundary w = u := by
      rw [boundary, hw, ← (D.strict_corner e he).1]
      dsimp only [w]
      ring
    have hl : D.boundaryNaturalLift z w := by
      have hp : (0 : ℤ) < f.length.val := by exact_mod_cast f.length_pos
      constructor
      · rw [hbw]; dsimp only [z]; lia
      · dsimp only [z, w]; lia
    refine (D.mem_naturalPairs_iff _).mpr ⟨D.edgeFromLift z w hl, ?_⟩
    rw [D.edgeFromLift_tail, D.edgeFromLift_head, hz, hw]
  · intro h
    obtain ⟨f, hf⟩ := (D.mem_naturalPairs_iff _).mp h
    obtain ⟨hft, hfh⟩ := Prod.mk.inj hf
    let w : ℤ := e.head.val
    let u : ℤ := w - e.length.val
    let z : ℤ := w - f.length.val
    have hw : e.head = D.residue w := (Orientation.residue_intCast_eq e.head).symm
    have hu : e.tail = D.residue u :=
      D.residue_tail_of_length hw (by dsimp only [u]; ring)
    have hz : v = D.residue z := hft.symm.trans
      (D.residue_tail_of_length (hfh.trans hw) (by dsimp only [z]; ring))
    have hlen : f.length.val ≤ e.length.val := by
      have hfarea := f.length_le_area
      rw [hfh, ← (D.strict_corner e he).1] at hfarea
      exact hfarea
    have hne : f.length.val ≠ e.length.val := by
      intro hfe
      have hzu : z = u := by dsimp only [z, u]; rw [hfe]
      exact hvt (hz.trans ((congrArg D.residue hzu).trans hu.symm))
    have hlt : (f.length.val : ℤ) < e.length.val := by
      exact_mod_cast (lt_of_le_of_ne hlen hne)
    have hbw : D.boundary w = u := by
      rw [boundary, ← hw, ← (D.strict_corner e he).1]
    have hzw : z < w := by
      have hp : (0 : ℤ) < f.length.val := by exact_mod_cast f.length_pos
      dsimp only [z]
      lia
    have hl : D.boundaryNaturalLift u z := by
      constructor
      · exact (D.boundary_monotone hzw.le).trans_eq hbw
      · dsimp only [z, u]; lia
    refine (D.mem_naturalPairs_iff _).mpr ⟨D.edgeFromLift u z hl, ?_⟩
    rw [D.edgeFromLift_tail, D.edgeFromLift_head, ← hu, ← hz]

/-- For a third vertex the natural edges in the corner equivalence are normal. -/
theorem normalPairs_across_strict_corner_iff {e : Edge D.area}
    (he : e ∈ D.strict) (v : Fin n) (hvt : v ≠ e.tail) (hvh : v ≠ e.head) :
    (e.tail, v) ∈ D.pairGraph.normalEdges ↔
      (v, e.head) ∈ D.pairGraph.normalEdges := by
  have hleft : (e.tail, v) ∉ D.pairGraph.strictEdges := by
    intro h
    obtain ⟨f, hf, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hp
    have hfe := D.strict_edge_eq_of_tail_eq hf he ht
    exact hvh (hh.symm.trans (congrArg Edge.head hfe))
  have hright : (v, e.head) ∉ D.pairGraph.strictEdges := by
    intro h
    obtain ⟨f, hf, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hp
    have hfe := D.strict_edge_eq_of_head_eq hf he hh
    exact hvt (ht.symm.trans (congrArg Edge.tail hfe))
  simpa only [D.normalPairs_eq_sdiff, Finset.mem_sdiff, hleft, hright, not_false_eq_true,
    and_true] using D.naturalPairs_across_strict_corner_iff he v hvt hvh

end VerticalStripLLT.Circular.Diagram

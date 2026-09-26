import VerticalStripLLT.Circular.AliasArea
import VerticalStripLLT.Circular.StrictEdgeInjectivity
import VerticalStripLLT.Circular.EdgeBounds

/-! A valid target for overlapping initial and terminal ND edge orbits. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)
  (i : Fin n) (f : Edge D.area) (hf : f ∈ D.strict)
  (hi : D.area.next i = f.head)
  (harea : D.area.area f.head = D.area.area i + 1)
  (hlen : 3 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

noncomputable def aliasArea : CircularArea n :=
  D.area.aliasLower i f.head hi harea (by rw [← (D.strict_corner f hf).1]; exact hlen) hgap

noncomputable def aliasIncl : Edge (D.aliasArea i f hf hi harea hlen hgap) ↪ Edge D.area where
  toFun g := ⟨g.val, g.property.1,
    g.property.2.trans (D.area.aliasLowerValues_le i f.head g.head)⟩
  inj' := by intro a b h; exact Subtype.ext (congrArg (fun a : Edge D.area => a.val) h)

noncomputable def aliasEdge : Edge (D.aliasArea i f hf hi harea hlen hgap) :=
  ⟨(i, ⟨D.area.area i - 1, (Nat.sub_le _ _).trans_lt (D.area.bound i)⟩), by
    have hc := (D.strict_corner f hf).1
    constructor
    · change 0 < D.area.area i - 1
      lia
    · change D.area.area i - 1 ≤ D.area.aliasLowerValues i f.head i
      rw [D.area.aliasLowerValues_left]⟩

theorem aliasEdge_corner : IsCorner (D.aliasEdge i f hf hi harea hlen hgap) := by
  have hne : f.head ≠ i := by intro h; rw [h] at harea; lia
  constructor
  · change D.area.area i - 1 = D.area.aliasLowerValues i f.head i
    rw [D.area.aliasLowerValues_left]
  · change D.area.aliasLowerValues i f.head (D.area.next i) ≤
      D.area.aliasLowerValues i f.head i
    rw [hi, D.area.aliasLowerValues_left, D.area.aliasLowerValues_right i f.head hne]
    lia

theorem aliasIncl_strict_corner (hheads : ∀ g ∈ D.strict, g.head ≠ i)
    (g : Edge (D.aliasArea i f hf hi harea hlen hgap))
    (hg : D.aliasIncl i f hf hi harea hlen hgap g ∈ D.strict) : IsCorner g := by
  have hc := D.strict_corner _ hg
  have hgi : g.head ≠ i := hheads _ hg
  have hgf : g.head ≠ f.head := by
    intro h
    have hne : f.head ≠ i := by intro h; rw [h] at harea; lia
    have hbound : g.length.val ≤ D.area.aliasLowerValues i f.head g.head := g.property.2
    rw [h, D.area.aliasLowerValues_right i f.head hne] at hbound
    have hc' : g.length.val = D.area.area g.head := hc.1
    rw [h] at hc'
    have hpos := g.length_pos
    lia
  constructor
  · change g.length.val = D.area.aliasLowerValues i f.head g.head
    rw [D.area.aliasLowerValues_other i f.head g.head hgi hgf]
    exact hc.1
  · change D.area.aliasLowerValues i f.head (D.area.next g.head) ≤
      D.area.aliasLowerValues i f.head g.head
    rw [D.area.aliasLowerValues_other i f.head g.head hgi hgf]
    exact (D.area.aliasLowerValues_le i f.head _).trans hc.2

/-- Retain all surviving strict edges and insert the doubly trimmed root. -/
noncomputable def aliasTarget (hheads : ∀ g ∈ D.strict, g.head ≠ i) : Diagram n where
  area := D.aliasArea i f hf hi harea hlen hgap
  strict := insert (D.aliasEdge i f hf hi harea hlen hgap)
    (Finset.univ.filter fun g => D.aliasIncl i f hf hi harea hlen hgap g ∈ D.strict)
  strict_corner := by
    intro g hg
    rcases Finset.mem_insert.mp hg with h | h
    · subst g
      exact D.aliasEdge_corner i f hf hi harea hlen hgap
    · exact D.aliasIncl_strict_corner i f hf hi harea hlen hgap hheads g
        (Finset.mem_filter.mp h).2

theorem aliasTarget_area (hheads : ∀ g ∈ D.strict, g.head ≠ i) :
    (D.aliasTarget i f hf hi harea hlen hgap hheads).area.area =
      Function.update (Function.update D.area.area f.head (D.area.area f.head - 2))
        i (D.area.area i - 1) := rfl

end VerticalStripLLT.Circular.Diagram

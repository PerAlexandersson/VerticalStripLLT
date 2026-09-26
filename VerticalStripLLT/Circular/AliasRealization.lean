import VerticalStripLLT.Circular.AliasMeasure
import VerticalStripLLT.Circular.ContactEndpoints

/-! The overlapping terminal ND branch supplies a valid area-decreasing target. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem nonstrict_zero_gap_area_succ {x : ℤ}
    (hx : ¬ D.strictAt x) (hg : D.eastGap x = 0) :
    D.area.area (D.residue (x + 1)) = D.area.area (D.residue x) + 1 := by
  simp only [eastGap, hx, ↓reduceIte, sub_zero, boundary] at hg
  lia

theorem EligibleDE.alias_area_ge_three {t x : ℤ} (ht : D.EligibleDE t)
    (h : ReverseBounce D t x) (halias : D.residue t = D.residue (x + 1)) :
    3 ≤ D.area.area (D.residue t) := by
  by_contra hsmall
  have heq : D.area.area (D.residue t) = 2 := by have := ht.2.1; lia
  have hb : D.boundary t = t - 2 := by simp [boundary, heq]
  have hr : D.residue (D.boundary t + 1) = D.residue x := by
    apply D.area.next_injective
    rw [← D.residue_succ, ← D.residue_succ, hb]
    convert halias using 1
    congr 1
    ring
  obtain ⟨v, hv, _⟩ := Relation.TransGen.head'_iff.mp (h.selected_path ht.1)
  exact ht.parallel_end_free D v (hr.symm ▸ hv)

/-- The target is geometric data with a proved decrease; no LLT identity is assumed. -/
theorem exists_aliasTarget_of_reverseBounce {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounce D t x)
    (hx : ¬ D.strictAt x) (halias : D.residue t = D.residue (x + 1)) :
    ∃ Q : Diagram n,
      Q.area.area = Function.update
        (Function.update D.area.area (D.residue t) (D.area.area (D.residue t) - 2))
          (D.residue x) (D.area.area (D.residue x) - 1) ∧
      Q.strict.card = D.strict.card ∧ Q.doubledArea + 6 = D.doubledArea := by
  obtain ⟨f, hf, fh⟩ := ht.1
  have hi : D.area.next (D.residue x) = f.head := by
    rw [← D.residue_succ, ← halias, fh]
  have harea : D.area.area f.head = D.area.area (D.residue x) + 1 := by
    rw [fh, halias]
    exact D.nonstrict_zero_gap_area_succ hx h.terminal_gap.1
  have hlen : 3 ≤ f.length.val := by
    rw [(D.strict_corner f hf).1, fh]
    exact ht.alias_area_ge_three D h halias
  have hgap : D.area.area (D.area.next f.head) < D.area.area f.head := by
    have hh := ht.boundary_gap D
    simp only [boundary, D.residue_succ, ← fh] at hh
    lia
  have hheads : ∀ g ∈ D.strict, g.head ≠ D.residue x := by
    intro g hg hh
    exact hx ⟨g, hg, hh⟩
  refine ⟨D.aliasTarget (D.residue x) f hf hi harea hlen hgap hheads, ?_,
    D.aliasTarget_strict_card _ f hf hi harea hlen hgap hheads,
    D.aliasTarget_doubledArea _ f hf hi harea hlen hgap hheads⟩
  rw [D.aliasTarget_area, fh]

end VerticalStripLLT.Circular.Diagram

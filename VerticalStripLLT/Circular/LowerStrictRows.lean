import VerticalStripLLT.Circular.LowerStrict
import VerticalStripLLT.Circular.CornerDeleteRows

/-! Row incidences and lifted boundaries after a lower-strict move. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem lowerStrict_strictAt_iff (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i)
    (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) (z : ℤ) :
    (D.lowerStrict i g hg gh heq hpos).strictAt z ↔
      (D.strictAt z ∧ D.residue z ≠ g.head) ∨ D.residue z = i := by
  let E := D.deleteCorner g (D.strict_corner g hg)
  let h := D.loweredEdge i g hg gh heq hpos
  let L := D.lowerStrict i g hg gh heq hpos
  have hres : L.residue z = D.residue z := rfl
  change (∃ e ∈ insert h E.strict, e.head = L.residue z) ↔ _
  constructor
  · rintro ⟨e, he, hh⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · right
      rw [D.loweredEdge_head i g hg gh heq hpos] at hh
      exact hres.symm.trans hh.symm
    · left
      apply (D.deleteStrictCorner_strictAt_iff g hg z).mp
      exact ⟨e, he, hh⟩
  · rintro (⟨hs, hz⟩ | hz)
    · rcases (D.deleteStrictCorner_strictAt_iff g hg z).mpr ⟨hs, hz⟩ with
        ⟨e, he, hh⟩
      exact ⟨e, Finset.mem_insert_of_mem he, hh⟩
    · refine ⟨h, Finset.mem_insert_self _ _, ?_⟩
      rw [D.loweredEdge_head i g hg gh heq hpos]
      exact hz.symm

theorem lowerStrict_boundary (i : Fin n) (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.area.next i)
    (heq : D.area.area g.head = D.area.area i + 1)
    (hpos : 1 ≤ D.area.area i) (z : ℤ) :
    (D.lowerStrict i g hg gh heq hpos).boundary z =
      D.boundary z + if D.residue z = g.head then 1 else 0 := by
  exact D.deleteCorner_boundary g (D.strict_corner g hg) z

end VerticalStripLLT.Circular.Diagram

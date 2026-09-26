import VerticalStripLLT.Circular.DeleteBounceTransport
import VerticalStripLLT.Circular.DDChildEligibility

/-! The complete smaller child produced by deleting the last parallel DD corner. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem EligibleDE.terminal_rows_ne {t x : ℤ} (ht : D.EligibleDE t)
    (ha : D.edgeData.Admissible ∅)
    (hp : Relation.TransGen (D.edgeData.selected ∅)
      (D.residue x) (D.residue (D.boundary t))) :
    D.residue x ≠ D.residue (D.boundary t + 1) ∧
      D.residue (x + 1) ≠ D.residue (D.boundary t + 1) := by
  constructor
  · intro heq
    obtain ⟨v, hv, _⟩ := Relation.TransGen.head'_iff.mp hp
    exact ht.parallel_end_free D v (heq ▸ hv)
  · intro heq
    have hrow : D.residue x = D.residue (D.boundary t) := by
      apply D.area.next_injective
      simpa only [D.residue_succ] using heq
    exact ha _ (hrow ▸ hp)

/-- The deletion child has one fewer DD contact and exactly the same terminal type. -/
theorem delete_dd_child {t x : ℤ} {k : ℕ}
    (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x (k + 1))
    (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.residue (D.boundary t + 1)) :
    let E := D.deleteCorner g (D.strict_corner g hg)
    E.EligibleDE (D.boundary t) ∧
      ReverseBounceN E (D.boundary t) x k ∧
      (E.strictAt x ↔ D.strictAt x) ∧
      (E.strictAt (x + 1) ↔ D.strictAt (x + 1)) ∧
      E.edgeData.Admissible ∅ := by
  obtain ⟨hz, hc, _, child⟩ := (D.reverseBounceN_succ_iff).mp h
  have hpath := child.selected_path D hc
  obtain ⟨hx, hx1⟩ := ht.terminal_rows_ne D ha hpath
  refine ⟨D.deleteParallelCorner_eligibleDE ht hc hz g hg gh,
    child.delete_parallel_transport D ht ha g hg gh hc .refl, ?_, ?_,
    D.deleteStrictCorner_admissible g hg ha⟩
  · rw [D.deleteStrictCorner_strictAt_iff g hg x, gh, and_iff_left hx]
  · rw [D.deleteStrictCorner_strictAt_iff g hg (x + 1), gh, and_iff_left hx1]

end VerticalStripLLT.Circular.Diagram

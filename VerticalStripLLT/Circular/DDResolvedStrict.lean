import VerticalStripLLT.Circular.DDLocalData
import VerticalStripLLT.Circular.DNStrictRows

/-! Resolving the last DD contact removes exactly its main strict row. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem resolved_strictAt_iff (z : ℤ) :
    B.resolved.strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t) := by
  unfold resolved Diagram.ddResolved
  rw [Diagram.dnSuccessor_strictAt_iff, D.unstrict_strictAt_iff]
  change ((D.strictAt z ∧ D.residue z ≠ B.g.head) ∧ D.residue z ≠ B.e.head) ∨
    D.residue z = D.area.next B.e.head ↔ _
  rw [← B.head, ← B.eh]
  have hne : B.g.head ≠ B.e.head := fun h =>
    B.heg (D.strict_edge_eq_of_head_eq B.hg B.he h).symm
  have hstrict : D.residue z = B.g.head → D.strictAt z :=
    fun h => ⟨B.g, B.hg, h.symm⟩
  have hne' : D.residue z = B.g.head → D.residue z ≠ B.e.head :=
    fun h he => hne (h.symm.trans he)
  tauto

end VerticalStripLLT.Circular.Diagram.DDLocalData

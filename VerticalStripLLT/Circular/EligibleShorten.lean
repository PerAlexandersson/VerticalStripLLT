import VerticalStripLLT.Circular.ShortenStrictRows
import VerticalStripLLT.Circular.ShortenStrictMeasure

/-! Canonical root shortening from an actual eligible DE row. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n) (t : ℤ) (ht : D.EligibleDE t)

noncomputable def eligibleEdge : Edge D.area := Classical.choose ht.1

theorem eligibleEdge_mem : D.eligibleEdge t ht ∈ D.strict :=
  (Classical.choose_spec ht.1).1

theorem eligibleEdge_head : (D.eligibleEdge t ht).head = D.residue t :=
  (Classical.choose_spec ht.1).2

theorem eligibleEdge_length : 2 ≤ (D.eligibleEdge t ht).length.val := by
  rw [(D.strict_corner _ (D.eligibleEdge_mem t ht)).1, D.eligibleEdge_head]
  exact ht.2.1

theorem eligibleEdge_gap :
    D.area.area (D.area.next (D.eligibleEdge t ht).head) <
      D.area.area (D.eligibleEdge t ht).head := by
  have hh := ht.boundary_gap D
  rw [D.eligibleEdge_head]
  simp only [boundary, D.residue_succ] at hh
  lia

noncomputable def shortenEligible : Diagram n :=
  D.shortenStrict (D.eligibleEdge t ht) (D.eligibleEdge_mem t ht)
    (D.eligibleEdge_length t ht) (D.eligibleEdge_gap t ht)

theorem shortenEligible_area :
    (D.shortenEligible t ht).area.area =
      Function.update D.area.area (D.residue t) (D.area.area (D.residue t) - 1) := by
  change Function.update D.area.area (D.eligibleEdge t ht).head
    (D.area.area (D.eligibleEdge t ht).head - 1) = _
  rw [D.eligibleEdge_head]

theorem shortenEligible_strictAt_iff (z : ℤ) :
    (D.shortenEligible t ht).strictAt z ↔ D.strictAt z :=
  D.shortenStrict_strictAt_iff _ _ _ _ z

theorem shortenEligible_doubledArea :
    (D.shortenEligible t ht).doubledArea + 2 = D.doubledArea :=
  D.shortenStrict_doubledArea _ _ _ _

end VerticalStripLLT.Circular.Diagram

import VerticalStripLLT.Circular.EligibleShorten
import VerticalStripLLT.Circular.CornerDeleteRows

/-! Preservation of eligible rows under the local corner moves. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem deleteStrictCorner_preserves_eligible {t : ℤ} (ht : D.EligibleDE t)
    (g : Edge D.area) (hg : g ∈ D.strict) (hne : D.residue t ≠ g.head) :
    (D.deleteCorner g (D.strict_corner g hg)).EligibleDE t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D.deleteStrictCorner_strictAt_iff g hg]
    exact ⟨ht.1, hne⟩
  · change Function.update D.area.area g.head (D.area.area g.head - 1)
      (D.residue t) ≥ 2
    rw [Function.update_of_ne hne]
    exact ht.2.1
  · rw [D.deleteStrictCorner_eastGap g hg t]
    have hnonneg :
        0 ≤ if D.residue (t + 1) = g.head then (1 : ℤ) else 0 := by
      split <;> norm_num
    have hpos := ht.2.2
    lia

theorem shortenEligible_preserves_eligible {s t : ℤ} (hs : D.EligibleDE s)
    (ht : D.EligibleDE t) (hne : D.residue t ≠ D.residue s) :
    (D.shortenEligible s hs).EligibleDE t := by
  let e := D.eligibleEdge s hs
  have he : e ∈ D.strict := D.eligibleEdge_mem s hs
  have hlen : 2 ≤ e.length.val := D.eligibleEdge_length s hs
  have hgap := D.eligibleEdge_gap s hs
  have hehead : e.head = D.residue s := D.eligibleEdge_head s hs
  refine ⟨?_, ?_, ?_⟩
  · exact (D.shortenEligible_strictAt_iff s hs t).mpr ht.1
  · change (D.shortenEligible s hs).area.area (D.residue t) ≥ 2
    rw [D.shortenEligible_area, Function.update_of_ne hne]
    exact ht.2.1
  · have hb0 := D.shortenStrict_boundary e he hlen hgap t
    change (D.shortenStrict e he hlen hgap).eastGap t > 0
    have hb1 := D.shortenStrict_boundary e he hlen hgap (t + 1)
    have hst := D.shortenStrict_strictAt_iff e he hlen hgap t
    unfold eastGap
    rw [hb0, hb1, hst]
    rw [hehead]
    have hzero : ¬ D.residue t = D.residue s := hne
    have hnonneg :
        0 ≤ if D.residue (t + 1) = D.residue s then (1 : ℤ) else 0 := by
      split <;> norm_num
    simp only [hzero, ↓reduceIte]
    have hpos := ht.2.2
    unfold eastGap at hpos
    lia

end VerticalStripLLT.Circular.Diagram

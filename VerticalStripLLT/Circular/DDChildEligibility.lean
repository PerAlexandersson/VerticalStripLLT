import VerticalStripLLT.Circular.CornerDeleteRows
import VerticalStripLLT.Circular.BounceSearch
import Mathlib.Tactic.Linarith

/-! Eligibility and acyclicity after deleting the parallel DD corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem deleteParallelCorner_eligibleDE
    {t : ℤ} (ht : D.EligibleDE t) (hc : D.strictAt (D.boundary t))
    (hz : D.eastGap (D.boundary t) = 0)
    (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.residue (D.boundary t + 1)) :
    (D.deleteCorner g (D.strict_corner g hg)).EligibleDE (D.boundary t) := by
  let E := D.deleteCorner g (D.strict_corner g hg)
  have hn : 3 ≤ n := by
    have ha := ht.2.1
    have hb := D.area.bound (D.residue t)
    lia
  have hres : D.residue (D.boundary t) ≠ g.head := by
    rw [gh]
    exact D.residue_p_ne_succ (by lia) _
  have hstrictE : E.strictAt (D.boundary t) := by
    rw [D.deleteStrictCorner_strictAt_iff g hg]
    exact ⟨hc, hres⟩
  have hgapE : E.eastGap (D.boundary t) > 0 := by
    rw [D.deleteStrictCorner_eastGap g hg]
    simp [gh, hz]
  have harea : 2 ≤ D.area.area (D.residue (D.boundary t)) := by
    have hstep : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t) + 1 := by
      unfold eastGap at hz
      simp [hc] at hz
      lia
    have hc1 : D.strictAt (D.boundary t + 1) := by
      exact ⟨g, hg, gh⟩
    have hc2 := D.strictAt_boundary_lt hc1
    have hroot : D.boundary t = t - (D.area.area (D.residue t) : ℤ) := rfl
    have hmono := D.boundary_monotone (show D.boundary t + 2 ≤ t by
      dsimp [Diagram.boundary]
      have ha := ht.2.1
      lia)
    have hb0 : D.boundary (D.boundary t + 2) ≤ D.boundary t := by
      exact hmono
    rw [show D.boundary t + 1 + 1 = D.boundary t + 2 by ring] at hc2
    have hbase : D.boundary (D.boundary t) =
        D.boundary t - (D.area.area (D.residue (D.boundary t)) : ℤ) := rfl
    lia
  have hareaE : E.area.area (E.residue (D.boundary t)) =
      D.area.area (D.residue (D.boundary t)) := by
    change E.area.area (D.residue (D.boundary t)) = _
    change (D.area.lowerAt g.head (corner_area_pos (D.strict_corner g hg))
      (D.strict_corner g hg).2).area (D.residue (D.boundary t)) = _
    rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hres]
  exact ⟨hstrictE, by rw [hareaE]; exact harea, hgapE⟩

theorem deleteStrictCorner_admissible
    (g : Edge D.area) (hg : g ∈ D.strict)
    (ha : D.edgeData.Admissible ∅) :
    (D.deleteCorner g (D.strict_corner g hg)).edgeData.Admissible ∅ := by
  intro v hv
  apply ha v
  refine Relation.TransGen.mono ?_ _ _ hv
  rintro u w ⟨e, he, hu, hw⟩
  have hes : e ∈ (D.deleteCorner g (D.strict_corner g hg)).strict := by
    simpa [Diagram.edgeData] using he
  have he' := (D.mem_deleteCorner_strict g (D.strict_corner g hg) e).mp hes
  refine ⟨D.cornerIncl g (D.strict_corner g hg) e,
    Finset.mem_union_left _ he', ?_, ?_⟩
  · exact hu
  · exact hw

end VerticalStripLLT.Circular.Diagram

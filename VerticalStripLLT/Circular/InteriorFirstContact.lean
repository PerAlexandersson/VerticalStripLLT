import VerticalStripLLT.Circular.InteriorRestart
import VerticalStripLLT.Circular.NNElimination
import VerticalStripLLT.Circular.DDRecurrences

set_option backward.isDefEq.respectTransparency false

/-! The interior-overlap ND branch when `x + 1` aliases the first main contact row:
the resolved DD child has a zero-DD NN restart, whose shortened child lies below `D`. -/

namespace VerticalStripLLT.Circular.Diagram

/-- The interior-overlap ND branch in the case where the terminal upper row `x + 1`
aliases the first main contact row `boundary t`.  Saturation is not needed here. -/
theorem expansion_of_nd_interior_overlap_first_contact {n : ℕ} (D : Diagram n)
    {t x : ℤ} {k : ℕ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hfirst : D.residue (D.boundary t) = D.residue (x + 1)) (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  obtain ⟨B⟩ := D.exists_ddLocalData ht h
  have hres : D.residue (D.boundary^[1] t) = D.residue (x + 1) := by
    rw [Function.iterate_one]; exact hfirst
  obtain ⟨hs, hb, hny⟩ :=
    B.oneBounce_restart_of_interior_overlap_at ht ha h hx hx1 le_rfl (by lia) hres
  have hxk : D.boundary^[k + 3 - 1] t = x := by
    rw [show k + 3 - 1 = (k + 1) + 1 by lia]
    exact ((D.reverseBounceN_iff_iterate).mp h).1.symm
  rw [hxk] at hb hny
  have hRa := B.resolved_admissible ht ha
  have hnx : ¬ B.resolved.strictAt x := fun h' => hx ((B.resolved_strictAt_iff x).mp h').1
  obtain ⟨hc, he⟩ := B.resolved.shifted_nn_of_counted hs hRa hb hnx hny
  have hsh := B.resolved.shortenEligible_doubledArea _ hs
  have hRA := B.resolved_doubledArea
  have hR : xQShift m (B.resolved.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion B.resolved) := by
    rw [hc m, he, map_mul, evalElementary_C, ih _ (by lia)]
  exact B.expansion_of_resolved m hR ih

end VerticalStripLLT.Circular.Diagram

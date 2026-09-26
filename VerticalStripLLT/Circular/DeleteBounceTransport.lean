import VerticalStripLLT.Circular.CountedBounce
import VerticalStripLLT.Circular.CornerDeleteRows
import VerticalStripLLT.Circular.ContactEndpoints
import VerticalStripLLT.Circular.RaiseStrict

/-! Counted reverse bounces survive deletion of the last parallel DD corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem EligibleDE.contact_rows_ne {t s : ℤ} (ht : D.EligibleDE t)
    (ha : D.edgeData.Admissible ∅) (hs : D.strictAt s)
    (hp : Relation.ReflTransGen (D.edgeData.selected ∅)
      (D.residue s) (D.residue (D.boundary t))) :
    D.residue s ≠ D.residue (D.boundary t + 1) ∧
      D.residue (D.boundary s) ≠ D.residue (D.boundary t + 1) ∧
      D.residue (D.boundary s + 1) ≠ D.residue (D.boundary t + 1) := by
  have hstep := D.selected_of_strictAt hs
  have hpath := Relation.TransGen.head' hstep hp
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hfull := Relation.TransGen.tail' hp (D.selected_of_strictAt ht.1)
    obtain ⟨v, hv, _⟩ := Relation.TransGen.head'_iff.mp hfull
    exact ht.parallel_end_free D v (heq ▸ hv)
  · intro heq
    exact ht.parallel_end_free D _ (heq ▸ hstep)
  · intro heq
    have hrow : D.residue (D.boundary s) = D.residue (D.boundary t) := by
      apply D.area.next_injective
      simpa only [D.residue_succ] using heq
    exact ha _ (hrow ▸ hpath)

theorem ReverseBounceN.delete_parallel_transport {t s x : ℤ} {k : ℕ}
    (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (g : Edge D.area) (hg : g ∈ D.strict)
    (gh : g.head = D.residue (D.boundary t + 1))
    (h : ReverseBounceN D s x k) (hs : D.strictAt s)
    (hp : Relation.ReflTransGen (D.edgeData.selected ∅)
      (D.residue s) (D.residue (D.boundary t))) :
    ReverseBounceN (D.deleteCorner g (D.strict_corner g hg)) s x k := by
  let E := D.deleteCorner g (D.strict_corner g hg)
  have hboundary (z : ℤ) (hz : D.residue z ≠ D.residue (D.boundary t + 1)) :
      E.boundary z = D.boundary z := by
    change (D.deleteCorner g (D.strict_corner g hg)).boundary z = _
    rw [D.deleteCorner_boundary, gh, ite_eq_right hz, add_zero]
  have hgap (z : ℤ) (hz : D.residue (z + 1) ≠ D.residue (D.boundary t + 1)) :
      E.eastGap z = D.eastGap z := by
    change (D.deleteCorner g (D.strict_corner g hg)).eastGap z = _
    rw [D.deleteStrictCorner_eastGap g hg z, gh, ite_eq_right hz, add_zero]
  have hstrict (z : ℤ) (hz : D.residue z ≠ D.residue (D.boundary t + 1)) :
      E.strictAt z ↔ D.strictAt z := by
    change (D.deleteCorner g (D.strict_corner g hg)).strictAt z ↔ _
    rw [D.deleteStrictCorner_strictAt_iff g hg z, gh, and_iff_left hz]
  induction h with
  | stop s hz hn =>
      obtain ⟨hsne, hune, hu1ne⟩ := ht.contact_rows_ne D ha hs hp
      have hb := hboundary s hsne
      change ReverseBounceN E s (D.boundary s) 0
      rw [← hb]
      apply ReverseBounceN.stop
      · rw [hb, hgap _ hu1ne]
        exact hz
      · rw [hb, hstrict _ hune, hstrict _ hu1ne]
        exact hn
  | @descend s x k hz hfirst hsecond child ih =>
      obtain ⟨hsne, hune, hu1ne⟩ := ht.contact_rows_ne D ha hs hp
      have hb := hboundary s hsne
      change ReverseBounceN E s x (k + 1)
      apply ReverseBounceN.descend
      · rw [hb, hgap _ hu1ne]
        exact hz
      · rw [hb, hstrict _ hune]
        exact hfirst
      · rw [hb, hstrict _ hu1ne]
        exact hsecond
      · rw [hb]
        exact ih hfirst (Relation.TransGen.head' (D.selected_of_strictAt hs) hp).to_reflTransGen

end VerticalStripLLT.Circular.Diagram

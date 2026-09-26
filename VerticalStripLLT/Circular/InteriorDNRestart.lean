import VerticalStripLLT.Circular.InteriorRestart
import VerticalStripLLT.Circular.OneBounceDNData

/-! Every deeper interior overlap restarts as an actual one-bounce DN datum. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

theorem resolved_strictAt_interior
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k : ℕ}
    (B : D.DDLocalData t) (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x (k + 1))
    {i : ℕ} (hi2 : 2 ≤ i) (hik : i ≤ k + 1) :
    B.resolved.strictAt (D.boundary^[k + 3 - i] t) := by
  obtain ⟨_, hdd, _, _⟩ := (D.reverseBounceN_iff_iterate).mp h
  have hr2 : 2 ≤ k + 3 - i := by lia
  have hrk : k + 3 - i ≤ k + 1 := by lia
  have hs := (hdd (k + 3 - i) (by lia) hrk).2.1
  have hne := bounce_residue_ne_contact ht.1 ha hdd (k + 3 - i) hr2 (by lia)
  exact (B.resolved_strictAt_iff _).mpr ⟨hs, hne⟩

theorem exists_oneBounceDNData_of_interior_overlap
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k : ℕ}
    (B : D.DDLocalData t) (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x (k + 1))
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    {i : ℕ} (hi2 : 2 ≤ i) (hik : i ≤ k + 1)
    (hires : D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    Nonempty (B.resolved.OneBounceDNData (D.boundary^[k + 2 - i] t)) := by
  have hrestart := B.oneBounce_restart_of_interior_overlap_at ht ha h hx hx1
    (by lia) hik hires
  have hstrict := B.resolved_strictAt_interior ht ha h hi2 hik
  exact exists_oneBounceDNData hrestart.1 hrestart.2.1 hstrict hrestart.2.2

end VerticalStripLLT.Circular.Diagram.DDLocalData

import VerticalStripLLT.Components.ForwardHRVBasic
import VerticalStripLLT.Components.SinkReachability
import VerticalStripLLT.Components.BlockCancellation

/-! Actual circular HRV fibers in the ordinary forward-edge case. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators
open Classical
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)
  (hforward : ∀ e : Edge D.area, e.tail < e.head)

include hforward

/-- A path to the maximal reachable root stays inside its actual HRV fiber. -/
theorem hrvFiber_reaches_root_forward (r : Fin n) {u : Fin n} (hu : θ.hrv u = r) :
    Relation.ReflTransGen
      (inducedStep (D.edgeData.selected θ.val) (Finset.univ.filter fun v => θ.hrv v = r))
      u r := by
  have hpath : Relation.ReflTransGen (D.edgeData.selected θ.val) u r := by
    simpa only [hu] using θ.hrv_reachable u
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a c hac hcr ih =>
    have hc : θ.hrv c = r := by
      have hupper := θ.hrv_le_of_reachable_forward hforward
        (Relation.ReflTransGen.single hac)
      have hlower := θ.reachable_le_hrv_of_forward hforward hcr
      rw [hu] at hupper
      exact le_antisymm hupper hlower
    exact (ih hc).head ⟨by simpa using hu, by simpa using hc, hac⟩

/-- The signed local mountain extractor equals one on each nonempty actual HRV fiber. -/
theorem hrvFiber_blockCancellation_forward (r : Fin n)
    (hB : (Finset.univ.filter fun v => θ.hrv v = r).Nonempty) :
    (∑ T ∈ ((Finset.univ.filter fun v => θ.hrv v = r).erase r).powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible (D.edgeData.selected θ.val)
          (blockWord (Finset.univ.filter fun v => θ.hrv v = r) T) then 1 else 0)) = 1 := by
  let B := Finset.univ.filter fun v => θ.hrv v = r
  have hr : r ∈ B := by
    obtain ⟨u, hu⟩ := hB
    have hu' := (Finset.mem_filter.mp hu).2
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, hu'] using
      θ.hrv_idempotent u
  have hmax : ∀ v ∈ B, v ≤ r := by
    intro v hv
    have hh := (Finset.mem_filter.mp hv).2
    simpa only [hh] using θ.reachable_le_hrv_of_forward hforward
      (u := v) Relation.ReflTransGen.refl
  have hsink := (reaches_iff_unique_induced_sink (D.edgeData.selected θ.val)
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) B hr).mpr
    (fun v hv => θ.hrvFiber_reaches_root_forward hforward r (Finset.mem_filter.mp hv).2)
  rw [blockCancellation_uniqueSink (D.edgeData.selected θ.val)
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) B r hr hmax]
  exact ite_eq_left hsink

end VerticalStripLLT.Circular.Orientation

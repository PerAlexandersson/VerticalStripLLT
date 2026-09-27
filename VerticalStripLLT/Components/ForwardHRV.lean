import VerticalStripLLT.Components.ShortEdges
import VerticalStripLLT.Components.SinkReachability
import VerticalStripLLT.Components.BlockCancellation
import VerticalStripLLT.Circular.ZeroAreaFibers

/-! Actual circular HRV fibers in the ordinary forward-edge case. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators
open Classical
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)
  (hforward : ∀ e : Edge D.area, e.tail < e.head)

include hforward

theorem selected_lt_of_forward {u v : Fin n} (h : D.edgeData.selected θ.val u v) :
    u < v := by
  obtain ⟨e, _, rfl, rfl⟩ := h
  exact hforward e

theorem selected_liftStep_of_forward {u v : Fin n}
    (h : D.edgeData.selected θ.val u v) :
    D.liftStep θ.val (u.val : ℤ) (v.val : ℤ) := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  exact ⟨e, he, D.naturalLift_of_tail_lt_head e (hforward e)⟩

theorem reachable_lift_of_forward {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    Relation.ReflTransGen (D.liftStep θ.val) (u.val : ℤ) (v.val : ℤ) := by
  exact h.lift (fun x => (x.val : ℤ)) (fun _ _ hs =>
    θ.selected_liftStep_of_forward hforward hs)

/-- Forward lifted walks starting in the canonical period remain canonical. -/
theorem liftReach_canonical_of_forward {u : Fin n} {w : ℤ}
    (h : Relation.ReflTransGen (D.liftStep θ.val) (u.val : ℤ) w) :
    ∃ v : Fin n, w = (v.val : ℤ) := by
  induction h with
  | refl => exact ⟨u, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨v, rfl⟩ := ih
    obtain ⟨e, _, ht, rfl⟩ := hstep
    rw [residue_intCast_eq] at ht
    have hn := (D.naturalLift_of_tail_lt_head e (hforward e)).2
    refine ⟨e.head, ?_⟩
    rw [ht]
    exact hn.symm

theorem liftedHRV_eq_coe_hrv_of_forward (u : Fin n) :
    θ.liftedHRV (u.val : ℤ) = ((θ.hrv u).val : ℤ) := by
  obtain ⟨v, hv⟩ := θ.liftReach_canonical_of_forward hforward
    (θ.liftedHRV_reachable (u.val : ℤ))
  have hh : θ.hrv u = v := by simp only [hrv, hv, residue_intCast_eq]
  rw [hh, hv]

/-- Numeric maximality is proved for the existing lifted HRV, not a replacement map. -/
theorem reachable_le_hrv_of_forward {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) : v ≤ θ.hrv u := by
  have hmax := θ.le_liftedHRV_of_reachable (θ.reachable_lift_of_forward hforward h)
  rw [θ.liftedHRV_eq_coe_hrv_of_forward hforward] at hmax
  exact_mod_cast hmax

theorem hrv_le_of_reachable_forward {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    θ.hrv v ≤ θ.hrv u :=
  θ.reachable_le_hrv_of_forward hforward (h.trans (θ.hrv_reachable v))

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

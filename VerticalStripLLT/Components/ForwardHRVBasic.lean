import VerticalStripLLT.Components.ShortEdges
import VerticalStripLLT.Circular.ZeroAreaFibers

/-! Forward structural facts for actual circular HRV fibers. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators
open Classical

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

/-! Forward lifted walks starting in the canonical period remain canonical. -/
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

/-! Numeric maximality is proved for the existing lifted HRV, not a replacement map. -/
theorem reachable_le_hrv_of_forward {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) : v ≤ θ.hrv u := by
  have hmax := θ.le_liftedHRV_of_reachable (θ.reachable_lift_of_forward hforward h)
  rw [θ.liftedHRV_eq_coe_hrv_of_forward hforward] at hmax
  exact_mod_cast hmax

theorem hrv_le_of_reachable_forward {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    θ.hrv v ≤ θ.hrv u :=
  θ.reachable_le_hrv_of_forward hforward (h.trans (θ.hrv_reachable v))

end VerticalStripLLT.Circular.Orientation

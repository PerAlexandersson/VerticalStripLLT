import VerticalStripLLT.Components.WordProof.HRVInitialSupport

/-! Fiber and support identities for the forward HRV scan. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped Classical
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)
  (hforward : ∀ e : Edge D.area, e.tail < e.head)

include hforward

theorem hrvInitialSupport_sdiff_hrvFiber (r : Fin n) :
    θ.hrvInitialSupport (r.val + 1) \
        (Finset.univ.filter (fun v => θ.hrv v = r)) =
      θ.hrvInitialSupport r := by
  ext v
  simp only [Finset.mem_sdiff, mem_hrvInitialSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hne⟩
    by_contra hnot
    have heq : θ.hrv v = r := by
      apply Fin.ext
      have hle : r.val ≤ (θ.hrv v).val := Nat.le_of_not_gt hnot
      lia
    exact hne heq
  · intro hlt
    refine ⟨by lia, ?_⟩
    intro heq
    rw [heq] at hlt
    lia

theorem hrvFiber_subset_hrvInitialSupport_succ (r : Fin n) :
    (Finset.univ.filter (fun v => θ.hrv v = r)) ⊆
      θ.hrvInitialSupport (r.val + 1) := by
  intro v hv
  apply (θ.mem_hrvInitialSupport (r.val + 1) v).mpr
  rw [(Finset.mem_filter.mp hv).2]
  exact Nat.lt_succ_self _

theorem no_selected_edge_hrvInitialSupport_to_hrvFiber (r : Fin n) :
    ∀ x ∈ θ.hrvInitialSupport r, ∀ y ∈
      (Finset.univ.filter (fun v => θ.hrv v = r)),
      ¬ D.edgeData.selected θ.val x y := by
  intro x hx y hy hxy
  have hle : θ.hrv y ≤ θ.hrv x :=
    θ.hrv_le_of_reachable_forward hforward (Relation.ReflTransGen.single hxy)
  have hle' : r.val ≤ (θ.hrv x).val := by
    apply Fin.le_iff_val_le_val.mp
    simpa only [(Finset.mem_filter.mp hy).2] using hle
  exact (Nat.not_lt_of_ge hle') ((θ.mem_hrvInitialSupport r x).mp hx)

theorem hrvFiber_max_le (r : Fin n)
    {v : Fin n} (hv : v ∈ Finset.univ.filter (fun u => θ.hrv u = r)) :
    v ≤ r := by
  have hvr := (Finset.mem_filter.mp hv).2
  simpa only [hvr] using θ.reachable_le_hrv_of_forward hforward
    (u := v) Relation.ReflTransGen.refl

theorem hrvFiber_unique_induced_sink (r : Fin n)
    (hr : r ∈ Finset.univ.filter (fun v => θ.hrv v = r)) :
    ∀ v ∈ Finset.univ.filter (fun u => θ.hrv u = r),
      sinkOn (D.edgeData.selected θ.val)
        (Finset.univ.filter (fun u => θ.hrv u = r)) v ↔ v = r := by
  let B := Finset.univ.filter (fun v => θ.hrv v = r)
  have hreach : ∀ v ∈ B,
      Relation.ReflTransGen
        (inducedStep (D.edgeData.selected θ.val) B) v r := by
    intro v hv
    exact θ.hrvFiber_reaches_root_forward hforward r
      (Finset.mem_filter.mp hv).2
  have hrB : r ∈ B := by
    simpa only [B] using hr
  have hsink := (reaches_iff_unique_induced_sink
    (D.edgeData.selected θ.val)
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) B hrB).mpr hreach
  intro v hv
  simpa only [B] using hsink v hv

theorem mem_hrvInitialSupport_succ_iff_hrv_self (r : Fin n) :
    r ∈ θ.hrvInitialSupport (r.val + 1) ↔ θ.hrv r = r := by
  constructor
  · intro hr
    apply Fin.ext
    have hlt := (θ.mem_hrvInitialSupport (r.val + 1) r).mp hr
    have hle : r.val ≤ (θ.hrv r).val := by
      exact Fin.le_iff_val_le_val.mp
        (θ.reachable_le_hrv_of_forward hforward
          (u := r) Relation.ReflTransGen.refl)
    lia
  · intro heq
    apply (θ.mem_hrvInitialSupport (r.val + 1) r).mpr
    rw [heq]
    exact Nat.lt_succ_self _

theorem hrvFiber_eq_empty_of_hrv_ne (r : Fin n) (hne : θ.hrv r ≠ r) :
    Finset.univ.filter (fun v => θ.hrv v = r) = ∅ := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  intro hv
  apply hne
  have hid := θ.hrv_idempotent v
  rw [hv] at hid
  exact hid

end VerticalStripLLT.Circular.Orientation

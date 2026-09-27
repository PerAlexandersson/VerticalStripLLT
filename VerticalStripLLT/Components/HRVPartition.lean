import VerticalStripLLT.Components.ForwardHRV

/-! HRV identification from an ordered partition into forward blocks. -/

namespace VerticalStripLLT.Components

open Classical

noncomputable section

variable {n k : ℕ} {D : Circular.Diagram n}

theorem hrv_eq_root_of_partition
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (B : Fin k → Finset (Fin n)) (root : Fin k → Fin n)
    (owner : Fin n → Fin k)
    (hroot_mem : ∀ i, root i ∈ B i)
    (hmax : ∀ i v, v ∈ B i → v ≤ root i)
    (howner_mem : ∀ v, v ∈ B (owner v))
    (howner_iff : ∀ i v, v ∈ B i ↔ owner v = i)
    (hroot_desc : StrictAnti root)
    (hcross : ∀ ⦃u v : Fin n⦄,
      D.edgeData.selected θ.val u v → owner u ≤ owner v)
    (hunique : ∀ i v,
      sinkOn (D.edgeData.selected θ.val) (B i) v ↔ v = root i)
    (i : Fin k) {v : Fin n} (hv : v ∈ B i) :
    θ.hrv v = root i := by
  let R : Fin n → Fin n → Prop := D.edgeData.selected θ.val
  have hinc : ∀ ⦃u v : Fin n⦄, R u v → u < v := by
    intro u v huv
    exact θ.selected_lt_of_forward hforward huv
  have hroot_le {i j : Fin k} (hij : i ≤ j) : root j ≤ root i := by
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (hroot_desc hij).le
  have howner_rtc {u v : Fin n}
      (hpath : Relation.ReflTransGen R u v) : owner u ≤ owner v := by
    induction hpath with
    | refl => exact le_rfl
    | tail _ hstep ih => exact ih.trans (hcross hstep)
  have hreach_local (j : Fin k) {u : Fin n} (hu : u ∈ B j) :
      Relation.ReflTransGen (inducedStep R (B j)) u (root j) := by
    have hroot : root j ∈ B j := hroot_mem j
    exact (reaches_iff_unique_induced_sink R hinc (B j) hroot).mp
      (fun w _ => hunique j w) u hu
  have hlocal : Relation.ReflTransGen R v (root i) := by
    exact Relation.ReflTransGen.mono
      (fun _ _ hstep => hstep.2.2) _ _ (hreach_local i hv)
  have hlow : root i ≤ θ.hrv v :=
    θ.reachable_le_hrv_of_forward hforward hlocal
  have hpath : Relation.ReflTransGen R v (θ.hrv v) :=
    θ.hrv_reachable v
  have howner_path : i ≤ owner (θ.hrv v) := by
    rw [← (howner_iff i v).mp hv]
    exact howner_rtc hpath
  have hu_bound : θ.hrv v ≤ root (owner (θ.hrv v)) :=
    hmax (owner (θ.hrv v)) (θ.hrv v) (howner_mem (θ.hrv v))
  have hroot_bound : root (owner (θ.hrv v)) ≤ root i :=
    hroot_le howner_path
  exact le_antisymm (hu_bound.trans hroot_bound) hlow

theorem hrv_eq_owner_root
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (B : Fin k → Finset (Fin n)) (root : Fin k → Fin n)
    (owner : Fin n → Fin k)
    (hroot_mem : ∀ i, root i ∈ B i)
    (hmax : ∀ i v, v ∈ B i → v ≤ root i)
    (howner_mem : ∀ v, v ∈ B (owner v))
    (howner_iff : ∀ i v, v ∈ B i ↔ owner v = i)
    (hroot_desc : StrictAnti root)
    (hcross : ∀ ⦃u v : Fin n⦄,
      D.edgeData.selected θ.val u v → owner u ≤ owner v)
    (hunique : ∀ i v,
      sinkOn (D.edgeData.selected θ.val) (B i) v ↔ v = root i) (v : Fin n) :
    θ.hrv v = root (owner v) := by
  exact hrv_eq_root_of_partition θ hforward B root owner hroot_mem hmax
    howner_mem howner_iff hroot_desc hcross hunique (owner v) (howner_mem v)

theorem hrv_fiber_eq_partition_block
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (B : Fin k → Finset (Fin n)) (root : Fin k → Fin n)
    (owner : Fin n → Fin k)
    (hroot_mem : ∀ i, root i ∈ B i)
    (hmax : ∀ i v, v ∈ B i → v ≤ root i)
    (howner_mem : ∀ v, v ∈ B (owner v))
    (howner_iff : ∀ i v, v ∈ B i ↔ owner v = i)
    (hroot_desc : StrictAnti root)
    (hcross : ∀ ⦃u v : Fin n⦄,
      D.edgeData.selected θ.val u v → owner u ≤ owner v)
    (hunique : ∀ i v,
      sinkOn (D.edgeData.selected θ.val) (B i) v ↔ v = root i)
    (i : Fin k) :
    Finset.univ.filter (fun v => θ.hrv v = root i) = B i := by
  ext v
  constructor
  · intro hv
    have hhv := (Finset.mem_filter.mp hv).2
    have hroot : root (owner v) = root i := by
      rw [← hrv_eq_owner_root θ hforward B root owner hroot_mem hmax
        howner_mem howner_iff hroot_desc hcross hunique v]
      exact hhv
    exact (howner_iff i v).mpr (hroot_desc.injective hroot)
  · intro hv
    have howner : owner v = i := (howner_iff i v).mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ v, ?_⟩
    rw [hrv_eq_owner_root θ hforward B root owner hroot_mem hmax howner_mem
      howner_iff hroot_desc hcross hunique v, howner]

end

end VerticalStripLLT.Components

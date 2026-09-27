import VerticalStripLLT.Components.ForwardHRV
import VerticalStripLLT.Components.AncestorBlock

/-!
# Initial supports of the actual forward HRV map

Cutting by the HRV root rather than by the vertex itself gives outgoing-closed
supports. At the next root, an incoming-closed block with that unique induced
sink is precisely the actual HRV fiber.
-/

namespace VerticalStripLLT.Circular.Orientation

open scoped Classical
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)

/-- Vertices whose actual highest reachable root has rank below `k`. -/
noncomputable def hrvInitialSupport (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => (θ.hrv v).val < k

@[simp]
theorem mem_hrvInitialSupport (k : ℕ) (v : Fin n) :
    v ∈ θ.hrvInitialSupport k ↔ (θ.hrv v).val < k := by
  simp only [hrvInitialSupport, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem hrvInitialSupport_zero : θ.hrvInitialSupport 0 = ∅ := by
  ext v
  simp [mem_hrvInitialSupport]

@[simp]
theorem hrvInitialSupport_n : θ.hrvInitialSupport n = Finset.univ := by
  ext v
  simp only [mem_hrvInitialSupport, Finset.mem_univ, iff_true]
  exact (θ.hrv v).isLt

theorem hrvInitialSupport_monotone : Monotone θ.hrvInitialSupport := by
  intro k l hkl v hv
  apply (θ.mem_hrvInitialSupport l v).mpr
  exact ((θ.mem_hrvInitialSupport k v).mp hv).trans_le hkl

/-- Advancing the root cutoff adds exactly the next HRV fiber. -/
theorem hrvInitialSupport_succ (k : ℕ) (hk : k < n) :
    θ.hrvInitialSupport (k + 1) = θ.hrvInitialSupport k ∪
      Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩) := by
  ext v
  simp only [Finset.mem_union, mem_hrvInitialSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    by_cases hlt : (θ.hrv v).val < k
    · exact Or.inl hlt
    · exact Or.inr (Fin.ext (by lia))
  · rintro (hlt | heq)
    · lia
    · rw [heq]
      exact Nat.lt_succ_self _

/-- Initial HRV support only contains vertices below the same rank cutoff. -/
theorem hrvInitialSupport_subset_lt
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (k : ℕ) :
    θ.hrvInitialSupport k ⊆ Finset.univ.filter (fun v => v.val < k) := by
  intro v hv
  have hmax : v.val ≤ (θ.hrv v).val :=
    θ.reachable_le_hrv_of_forward hforward (u := v) Relation.ReflTransGen.refl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hmax.trans_lt ((θ.mem_hrvInitialSupport k v).mp hv)⟩

/-- A selected path starting in initial HRV support remains in that support. -/
theorem hrvInitialSupport_reach_closed
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (k : ℕ)
    {u v : Fin n} (hu : u ∈ θ.hrvInitialSupport k)
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    v ∈ θ.hrvInitialSupport k := by
  apply (θ.mem_hrvInitialSupport k v).mpr
  have hle : (θ.hrv v).val ≤ (θ.hrv u).val :=
    θ.hrv_le_of_reachable_forward hforward h
  exact hle.trans_lt ((θ.mem_hrvInitialSupport k u).mp hu)

/-- The selected relation has no outgoing edge from the initial support to its complement. -/
theorem hrvInitialSupport_outgoing_closed
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (k : ℕ)
    {u v : Fin n} (hu : u ∈ θ.hrvInitialSupport k)
    (h : D.edgeData.selected θ.val u v) : v ∈ θ.hrvInitialSupport k :=
  θ.hrvInitialSupport_reach_closed hforward k hu (Relation.ReflTransGen.single h)

/-- The ancestors of the last allowed root inside initial support form exactly its fiber. -/
theorem hrvInitialSupport_ancestor_filter_eq
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (r : Fin n) :
    (θ.hrvInitialSupport (r.val + 1)).filter (fun v =>
      Relation.ReflTransGen
        (inducedStep (D.edgeData.selected θ.val) (θ.hrvInitialSupport (r.val + 1))) v r) =
      Finset.univ.filter (fun v => θ.hrv v = r) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvs, hvr⟩ := Finset.mem_filter.mp hv
    have hpath : Relation.ReflTransGen (D.edgeData.selected θ.val) v r :=
      Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ hvr
    have hlo : r.val ≤ (θ.hrv v).val := θ.reachable_le_hrv_of_forward hforward hpath
    have hhi := (θ.mem_hrvInitialSupport (r.val + 1) v).mp hvs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext (by lia)⟩
  · intro hv
    have hvr := (Finset.mem_filter.mp hv).2
    have hsub : (Finset.univ.filter fun u => θ.hrv u = r) ⊆
        θ.hrvInitialSupport (r.val + 1) := by
      intro u hu
      apply (θ.mem_hrvInitialSupport (r.val + 1) u).mpr
      rw [(Finset.mem_filter.mp hu).2]
      exact Nat.lt_succ_self _
    refine Finset.mem_filter.mpr ⟨hsub hv, ?_⟩
    exact Relation.ReflTransGen.mono
      (fun _ _ h => ⟨hsub h.1, hsub h.2.1, h.2.2⟩) _ _
      (θ.hrvFiber_reaches_root_forward hforward r hvr)

/-- A first block with the maximal root and incoming closure is the actual HRV fiber. -/
theorem block_eq_hrvFiber_of_initialSupport
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (U : Finset (Fin n)) (r : Fin n) (hr : r ∈ U)
    (hUS : U ⊆ θ.hrvInitialSupport (r.val + 1))
    (hmax : ∀ v ∈ U, v ≤ r)
    (hunique : ∀ v ∈ U, v ≠ r → ¬sinkOn (D.edgeData.selected θ.val) U v)
    (hclosed : ∀ x ∈ θ.hrvInitialSupport (r.val + 1), ∀ y ∈ U,
      D.edgeData.selected θ.val x y → x ∈ U) :
    U = Finset.univ.filter (fun v => θ.hrv v = r) := by
  calc
    U = (θ.hrvInitialSupport (r.val + 1)).filter (fun v =>
        Relation.ReflTransGen
          (inducedStep (D.edgeData.selected θ.val) (θ.hrvInitialSupport (r.val + 1))) v r) :=
      block_eq_ambient_ancestor_filter (D.edgeData.selected θ.val)
        (fun {_ _} h => θ.selected_lt_of_forward hforward h)
        (θ.hrvInitialSupport (r.val + 1)) U r hr hUS hmax hunique hclosed
    _ = Finset.univ.filter (fun v => θ.hrv v = r) :=
      θ.hrvInitialSupport_ancestor_filter_eq hforward r

end VerticalStripLLT.Circular.Orientation

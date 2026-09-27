import VerticalStripLLT.Components.SinkReachability

/-! Identifying a finite block by its induced root and incoming closure. -/

namespace VerticalStripLLT.Components

open Classical

noncomputable section

variable {V : Type*} [LinearOrder V]

theorem block_eq_ambient_ancestor_filter
    (R : V → V → Prop) (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (S U : Finset V) (r : V) (hr : r ∈ U) (hUS : U ⊆ S)
    (hmax : ∀ v ∈ U, v ≤ r)
    (hunique : ∀ v ∈ U, v ≠ r → ¬sinkOn R U v)
    (hclosed : ∀ x ∈ S, ∀ y ∈ U, R x y → x ∈ U) :
    U = S.filter (fun v =>
      Relation.ReflTransGen (inducedStep R S) v r) := by
  have hrsink : sinkOn R U r := by
    refine ⟨hr, ?_⟩
    intro w hw hrw
    exact (not_lt_of_ge (hmax w hw)) (hinc hrw)
  have hsinks : ∀ v ∈ U, sinkOn R U v ↔ v = r := by
    intro v hv
    constructor
    · intro h
      by_contra hne
      exact (hunique v hv hne) h
    · intro hvr
      subst v
      exact hrsink
  have hreachU : ∀ v ∈ U,
      Relation.ReflTransGen (inducedStep R U) v r :=
    (reaches_iff_unique_induced_sink R hinc U hr).mp
      (fun v hv => hsinks v hv)
  apply Finset.ext
  intro v
  constructor
  · intro hv
    apply Finset.mem_filter.mpr
    refine ⟨hUS hv, ?_⟩
    exact Relation.ReflTransGen.mono
      (fun x y hxy => ⟨hUS hxy.1, hUS hxy.2.1, hxy.2.2⟩)
      _ _ (hreachU v hv)
  · intro hv
    have hback {w : V} (hpath : Relation.ReflTransGen (inducedStep R S) w r) :
        w ∈ U := by
      induction hpath using Relation.ReflTransGen.head_induction_on with
      | refl => exact hr
      | @head a c hac hcr ih => exact hclosed a hac.1 c ih hac.2.2
    exact hback (Finset.mem_filter.mp hv).2

end

end VerticalStripLLT.Components

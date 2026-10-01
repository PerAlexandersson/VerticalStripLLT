import VerticalStripLLT.Components.DiagramProof.Relational.RelationalTransport
import VerticalStripLLT.Components.DiagramProof.Foundation.LocalIdentities

/-!
# Marked values along corresponding states

A correspondence that fixes the marked vertex preserves the marked strict-coloring
value and the marked HRV value. Inside a weak block the bijection preserves the
order, so the greatest reachable vertex is carried to the greatest reachable vertex.
Summing over the bijection of whole components gives the component values.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D E : Diagram n}

/-- The greatest reachable vertex in a forward diagram. -/
theorem hrv_eq_of_reachable_greatest (hD : Forward D) (θ : Orientation D)
    {u x : Fin n} (hx : Relation.ReflTransGen (D.edgeData.selected θ.val) u x)
    (hmax : ∀ v, Relation.ReflTransGen (D.edgeData.selected θ.val) u v → v ≤ x) :
    θ.hrv u = x :=
  le_antisymm (hmax _ (θ.hrv_reachable u)) (θ.reachable_le_hrv_of_forward hD hx)

namespace Corresponds

variable {π : Equiv.Perm (Fin n)} {θ : Orientation D} {θ' : Orientation E}

theorem le_iff (h : Corresponds π θ θ') {u v : Fin n} (huv : WeakReach θ u v) :
    u ≤ v ↔ π u ≤ π v := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, h.order u v huv, π.injective.eq_iff]

/-- The correspondence carries greatest reachable vertices. -/
theorem hrv (hD : Forward D) (hE : Forward E) (h : Corresponds π θ θ') (u : Fin n) :
    θ'.hrv (π u) = π (θ.hrv u) := by
  apply hrv_eq_of_reachable_greatest hE
  · exact (h.reachable_iff u _).mpr (θ.hrv_reachable u)
  · intro v' hv'
    obtain ⟨v, rfl⟩ := π.surjective v'
    have hv := (h.reachable_iff u v).mp hv'
    have hblock : WeakReach θ v (θ.hrv u) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (weakReach_of_reachable hv))
        (weakReach_of_reachable (θ.hrv_reachable u))
    exact (h.le_iff hblock).mp (θ.reachable_le_hrv_of_forward hD hv)

theorem fibreRelation_iff (hD : Forward D) (hE : Forward E) (h : Corresponds π θ θ')
    (u w : Fin n) :
    fibreRelation θ.hrv u w ↔ fibreRelation θ'.hrv (π u) (π w) := by
  unfold fibreRelation
  rw [h.hrv hD hE, h.hrv hD hE, π.injective.eq_iff]
  constructor
  · rintro ⟨hlt, heq⟩
    refine ⟨(h.order u w ?_).mp hlt, heq⟩
    exact Relation.EqvGen.trans _ _ _ (weakReach_of_reachable (θ.hrv_reachable u))
      (heq ▸ Relation.EqvGen.symm _ _ (weakReach_of_reachable (θ.hrv_reachable w)))
  · rintro ⟨hlt, heq⟩
    refine ⟨(h.order u w ?_).mpr hlt, heq⟩
    exact Relation.EqvGen.trans _ _ _ (weakReach_of_reachable (θ.hrv_reachable u))
      (heq ▸ Relation.EqvGen.symm _ _ (weakReach_of_reachable (θ.hrv_reachable w)))

theorem markedK_eq (h : Corresponds π θ θ') {v : Fin n} (hv : π v = v) (m : ℕ) (β : Fin m) :
    markedK θ' v m β = markedK θ v m β := by
  have key := markedRelationValue_relabel (E.edgeData.selected θ'.val)
    (D.edgeData.selected θ.val) π (fun u w => (h.selected u w).symm) v m β
  rw [hv] at key
  exact key.symm

theorem markedE_eq (hD : Forward D) (hE : Forward E) (h : Corresponds π θ θ') {v : Fin n}
    (hv : π v = v) (m : ℕ) (β : Fin m) :
    markedE θ' v m β = markedE θ v m β := by
  have key := markedRelationValue_relabel (fibreRelation θ'.hrv)
    (fibreRelation θ.hrv) π (h.fibreRelation_iff hD hE) v m β
  rw [hv] at key
  exact key.symm

theorem componentMarkedK_eq (hD : Forward D) (hE : Forward E) (h : Corresponds π θ θ')
    {v : Fin n} (hv : π v = v) (m : ℕ) (β : Fin m) :
    componentMarkedK θ' v m β = componentMarkedK θ v m β :=
  (h.sum_flipComponent hD hE _ _ fun _ _ hc => (hc.markedK_eq hv m β).symm).symm

theorem componentMarkedE_eq (hD : Forward D) (hE : Forward E) (h : Corresponds π θ θ')
    {v : Fin n} (hv : π v = v) (m : ℕ) (β : Fin m) :
    componentMarkedE θ' v m β = componentMarkedE θ v m β :=
  (h.sum_flipComponent hD hE _ _ fun _ _ hc => (hc.markedE_eq hD hE hv m β).symm).symm

end Corresponds

end

end VerticalStripLLT.Circular.DiagramProof

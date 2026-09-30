import VerticalStripLLT.Components.DiagramProof.FibreSignature
import VerticalStripLLT.Circular.HRVConjugacy

/-! Endpoint-fixed relabelings need preserve only the order of selected sinks. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D E : Diagram n}

/-- Forward greatest reachability is transported by any sink-order-preserving relabeling. -/
theorem hrv_relabel_of_sinkOrder (θ : Orientation D) (η : Orientation E)
    (hD : Forward D) (hE : Forward E) (σ : Fin n ≃ Fin n)
    (hrel : ∀ u v, D.edgeData.selected θ.val u v ↔
      E.edgeData.selected η.val (σ u) (σ v))
    (horder : ∀ u v, (∀ w, ¬ D.edgeData.selected θ.val u w) →
      (∀ w, ¬ D.edgeData.selected θ.val v w) → u ≤ v → σ u ≤ σ v)
    (u : Fin n) : η.hrv (σ u) = σ (θ.hrv u) := by
  have hf : ∀ a b, Relation.ReflTransGen (D.edgeData.selected θ.val) a b →
      Relation.ReflTransGen (E.edgeData.selected η.val) (σ a) (σ b) := by
    intro a b h
    exact h.lift σ (fun x y hs => (hrel x y).mp hs)
  have hb : ∀ a b, Relation.ReflTransGen (E.edgeData.selected η.val) a b →
      Relation.ReflTransGen (D.edgeData.selected θ.val) (σ.symm a) (σ.symm b) := by
    intro a b h
    exact h.lift σ.symm (fun x y hs => (hrel (σ.symm x) (σ.symm y)).mpr
      (by simpa only [Equiv.apply_symm_apply] using hs))
  have hback : Relation.ReflTransGen (D.edgeData.selected θ.val) u
      (σ.symm (η.hrv (σ u))) := by
    simpa only [Equiv.symm_apply_apply] using hb _ _ (η.hrv_reachable (σ u))
  have hsink : ∀ w, ¬ D.edgeData.selected θ.val (σ.symm (η.hrv (σ u))) w := by
    intro w hw
    apply η.hrv_is_sink (σ u) (σ w)
    simpa only [Equiv.apply_symm_apply] using (hrel _ _).mp hw
  apply le_antisymm
  · simpa only [Equiv.apply_symm_apply] using horder _ _ hsink
      (fun w => θ.hrv_is_sink u w) (θ.reachable_le_hrv_of_forward hD hback)
  · exact η.reachable_le_hrv_of_forward hE (hf _ _ (θ.hrv_reachable u))

/-- The marked coloring bijection transports K at any fixed endpoint. -/
theorem markedK_relabel (θ : Orientation D) (η : Orientation E) (σ : Fin n ≃ Fin n)
    (hrel : ∀ u w, D.edgeData.selected θ.val u w ↔
      E.edgeData.selected η.val (σ u) (σ w))
    (v : Fin n) (hfix : σ v = v) (m : ℕ) (β : Fin m) :
    markedK θ v m β = markedK η v m β := by
  have h := markedRelationValue_relabel (E.edgeData.selected η.val)
    (D.edgeData.selected θ.val) σ hrel v m β
  rw [hfix] at h
  exact h

/-- Fibre-size matching proves E transport even when interior fibre labels change order. -/
theorem markedE_relabel_of_sinkOrder (θ : Orientation D) (η : Orientation E)
    (hD : Forward D) (hE : Forward E) (σ : Fin n ≃ Fin n)
    (hrel : ∀ u w, D.edgeData.selected θ.val u w ↔
      E.edgeData.selected η.val (σ u) (σ w))
    (horder : ∀ u w, (∀ z, ¬ D.edgeData.selected θ.val u z) →
      (∀ z, ¬ D.edgeData.selected θ.val w z) → u ≤ w → σ u ≤ σ w)
    (v : Fin n) (hv : ∀ u, u ≤ v) (hfix : σ v = v) (m : ℕ) (β : Fin m) :
    markedE θ v m β = markedE η v m β := by
  have hH := hrv_relabel_of_sinkOrder θ η hD hE σ hrel horder
  have hcards (r : Fin n) :
      Fintype.card {u // θ.hrv u = r} = Fintype.card {u // η.hrv u = σ r} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact (θ.hrvFiber_card_conjugate η σ hH r).symm
  have hmark : σ (θ.hrv v) = η.hrv v := by
    simpa only [hfix] using (hH v).symm
  exact markedFibreValue_eq_of_matching_sizes θ.hrv η.hrv σ hcards v hv hmark m β

end VerticalStripLLT.Circular.DiagramProof

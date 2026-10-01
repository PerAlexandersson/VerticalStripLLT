import VerticalStripLLT.Components.DiagramProof.Preparation.SweepRestoration

/-! Actual-orientation adapters for replaying the two sweep directions. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Restore an outgoing trace using actual incoming flips. -/
theorem restore_orientationOutgoingSweep (hforward : Forward D)
    {a b c : Fin n} {θ η : Orientation D}
    (htrace : Relation.ReflTransGen
      (OutgoingSweepStep (fun ξ : Orientation D => D.edgeData.selected ξ.val) (Flip D) a b c)
      θ η)
    (Φ : (Fin n → Fin n → Prop) → Fin n → Fin n → Prop)
    (hcongr : ∀ R S, (∀ u v, R u v ↔ S u v) → ∀ u v, Φ R u v ↔ Φ S u v)
    (hlocal : ∀ R u v, a < u → v ≤ c → (Φ R u v ↔ R u v))
    (hold : ∀ R w, a < w → w < b → (Φ R a w ↔ R a w))
    (hcommute : ∀ R w, a < w → w < b → ∀ u v,
      Φ (exchangeRelation R a w w c) u v ↔ exchangeRelation (Φ R) a w w c u v)
    (ξ : Orientation D) (hcover : Cover ξ a c)
    (hξ : ∀ u v, D.edgeData.selected ξ.val u v ↔ Φ (D.edgeData.selected η.val) u v) :
    ∃ ζ : Orientation D, Relation.ReflTransGen (Flip D) ξ ζ ∧ Cover ζ a c ∧
      (∀ u v, D.edgeData.selected ζ.val u v ↔ Φ (D.edgeData.selected θ.val) u v) := by
  apply restore_outgoingSweep (fun ξ : Orientation D => D.edgeData.selected ξ.val) (Flip D)
    (fun ξ {_ _} hs => ξ.selected_lt_of_forward hforward hs) ?_
    htrace Φ hcongr hlocal hold hcommute ξ hcover hξ
  intro α x y z hyz hxz hxy
  obtain ⟨β, hmove, hlong, _, hrel⟩ :=
    exists_incomingSwap_of_covers hforward α x y z hyz hxz hxy
  exact ⟨β, hmove, hlong, hrel⟩

/-- Restore an incoming trace using actual outgoing flips in the reverse order. -/
theorem restore_orientationIncomingSweep (hforward : Forward D)
    {b c d : Fin n} {θ η : Orientation D}
    (htrace : Relation.ReflTransGen
      (OutgoingSweepStep (V := OrderDual (Fin n))
        (fun ξ : Orientation D => Function.swap (D.edgeData.selected ξ.val)) (Flip D) d c b)
      θ η)
    (Φ : (Fin n → Fin n → Prop) → Fin n → Fin n → Prop)
    (hcongr : ∀ R S, (∀ u v, R u v ↔ S u v) → ∀ u v, Φ R u v ↔ Φ S u v)
    (hlocal : ∀ R u v, b ≤ u → v < d → (Φ R u v ↔ R u v))
    (hold : ∀ R w, c < w → w < d → (Φ R w d ↔ R w d))
    (hcommute : ∀ R w, c < w → w < d → ∀ u v,
      Φ (exchangeRelation R w d b w) u v ↔ exchangeRelation (Φ R) w d b w u v)
    (ξ : Orientation D) (hcover : Cover ξ b d)
    (hξ : ∀ u v, D.edgeData.selected ξ.val u v ↔ Φ (D.edgeData.selected η.val) u v) :
    ∃ ζ : Orientation D, Relation.ReflTransGen (Flip D) ξ ζ ∧ Cover ζ b d ∧
      (∀ u v, D.edgeData.selected ζ.val u v ↔ Φ (D.edgeData.selected θ.val) u v) := by
  let Ψ : (OrderDual (Fin n) → OrderDual (Fin n) → Prop) →
      OrderDual (Fin n) → OrderDual (Fin n) → Prop :=
    fun R u v => Φ (Function.swap R) v u
  have hs := restore_outgoingSweep (V := OrderDual (Fin n))
    (fun α : Orientation D => Function.swap (D.edgeData.selected α.val)) (Flip D)
    (fun α {_ _} h => α.selected_lt_of_forward hforward h) ?_
    htrace Ψ ?_ ?_ ?_ ?_ ξ ((relationCover_dual b d).mpr hcover) (fun u v => hξ v u)
  · obtain ⟨ζ, hp, hcov, hrel⟩ := hs
    exact ⟨ζ, hp, (relationCover_dual b d).mp hcov, fun u v => hrel v u⟩
  · intro α x y z hyz hxz hxy
    obtain ⟨β, hmove, hlong, _, hrel⟩ := exists_outgoingSwap_of_covers hforward α z y x
      ((relationCover_dual (V := Fin n) z y).mp hyz)
      ((relationCover_dual (V := Fin n) z x).mp hxz) hxy
    refine ⟨β, hmove, (relationCover_dual (V := Fin n) z x).mpr hlong, ?_⟩
    intro u v
    simpa only [exchangeRelation, Function.swap, and_comm] using hrel v u
  · intro R S h u v
    exact hcongr _ _ (fun x y => h y x) v u
  · intro R u v hdu hvb
    exact hlocal (Function.swap R) v u hvb hdu
  · intro R w hdw hwc
    exact hold (Function.swap R) w hwc hdw
  · intro R w hdw hwc u v
    have h := hcommute (Function.swap R) w hwc hdw v u
    apply (hcongr _ _ ?_ v u).trans
    · simpa only [exchangeRelation, Ψ, and_comm] using h
    · intro x y
      simp only [exchangeRelation, Function.swap, and_comm]

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.Preparation.RelationExchange

/-!
# Restore an outgoing sweep after changing its exterior

The modified states are constructed by actual incoming moves. We do not assume
that an arbitrary relation transformation already defines an orientation. The
short cover is transferred on its own interval, and each reverse move preserves
the retained long cover for the next step.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V State : Type*} [LinearOrder V]

/-- Replay a sweep backward when the commuting change is invisible on short-cover intervals. -/
theorem restore_outgoingSweep
    (selected : State → V → V → Prop) (step : State → State → Prop)
    (hforward : ∀ θ ⦃u v⦄, selected θ u v → u < v)
    (hincoming : ∀ θ a b c, RelationCover (selected θ) b c →
      RelationCover (selected θ) a c → a < b →
      ∃ η, step θ η ∧ RelationCover (selected η) a c ∧
        (∀ u v, selected η u v ↔ exchangeRelation (selected θ) b c a b u v))
    {a b c : V} {θ η : State}
    (htrace : Relation.ReflTransGen (OutgoingSweepStep selected step a b c) θ η)
    (Φ : (V → V → Prop) → V → V → Prop)
    (hcongr : ∀ R S, (∀ u v, R u v ↔ S u v) → ∀ u v, Φ R u v ↔ Φ S u v)
    (hlocal : ∀ R u v, a < u → v ≤ c → (Φ R u v ↔ R u v))
    (hold : ∀ R w, a < w → w < b → (Φ R a w ↔ R a w))
    (hcommute : ∀ R w, a < w → w < b → ∀ u v,
      Φ (exchangeRelation R a w w c) u v ↔ exchangeRelation (Φ R) a w w c u v)
    (ξ : State) (hcover : RelationCover (selected ξ) a c)
    (hξ : ∀ u v, selected ξ u v ↔ Φ (selected η) u v) :
    ∃ ζ, Relation.ReflTransGen step ξ ζ ∧ RelationCover (selected ζ) a c ∧
      (∀ u v, selected ζ u v ↔ Φ (selected θ) u v) := by
  induction htrace generalizing ξ with
  | refl => exact ⟨ξ, Relation.ReflTransGen.refl, hcover, hξ⟩
  | @tail α β hpath hmove ih =>
    obtain ⟨w, haw, hwb, _, hsourceShort, hsourceLong, _, htargetShort, hswap⟩ := hmove
    have hshort : RelationCover (selected ξ) w c := by
      apply (relationCover_congr_on_interval (hforward β) (hforward ξ)
        (lo := w) (hi := c) ?_ le_rfl le_rfl).mp htargetShort
      intro u v hwu hvc
      exact ((hξ u v).trans (hlocal (selected β) u v (haw.trans_le hwu) hvc)).symm
    obtain ⟨ξ', hback, hcover', hbackRel⟩ := hincoming ξ a w c hshort hcover haw
    have horiginal : selected α a w := rel_of_relationCover (hforward α) hsourceShort
    have hnot : ¬ selected α w c := by
      intro hwc
      exact hsourceLong.2.2 w haw htargetShort.1
        ⟨hsourceShort.2.1, Relation.ReflTransGen.single hwc⟩
    have htransformed : Φ (selected α) a w := (hold (selected α) w haw hwb).mpr horiginal
    have htransformedNot : ¬ Φ (selected α) w c := fun h =>
      hnot ((hlocal (selected α) w c haw le_rfl).mp h)
    have hcurrent : ∀ u v, selected ξ u v ↔
        exchangeRelation (Φ (selected α)) a w w c u v := by
      intro u v
      exact (hξ u v).trans
        ((hcongr (selected β) (exchangeRelation (selected α) a w w c) hswap u v).trans
          (hcommute (selected α) w haw hwb u v))
    have hrestored : ∀ u v, selected ξ' u v ↔ Φ (selected α) u v := by
      intro u v
      exact (hbackRel u v).trans
        ((exchangeRelation_congr hcurrent w c a w u v).trans
          (exchangeRelation_inverse _ htransformed htransformedNot u v))
    obtain ⟨ζ, hremaining, hfinalCover, hfinal⟩ := ih ξ' hcover' hrestored
    exact ⟨ζ, (Relation.ReflTransGen.single hback).trans hremaining, hfinalCover, hfinal⟩

end VerticalStripLLT.Circular.DiagramProof

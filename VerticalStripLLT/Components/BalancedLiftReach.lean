import VerticalStripLLT.Components.BalancedLifts
import VerticalStripLLT.Circular.LiftCover

/-!
# Reachability at compatible chosen lifts

Every selected lifted path starting at a chosen lift stays among the chosen
lifts. Consequently the full integer-cover condition is exactly the finite
cover condition ordered by those lifts, even when they span several periods.
-/

namespace VerticalStripLLT.Circular.Orientation

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)
variable {q : Fin n → ℤ}

/-- Selected edges and integer steps agree at the compatible chosen positions. -/
theorem liftStep_chosen_iff (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) {u v : Fin n} :
    D.liftStep θ.val (q u) (q v) ↔ D.edgeData.selected θ.val u v := by
  constructor
  · intro h
    simpa only [hq] using D.liftStep_selected h
  · rintro ⟨e, he, ht, hh⟩
    change e.tail = u at ht
    change e.head = v at hh
    have heq : q e.head - q e.tail = (e.length.val : ℤ) := hp e he
    rw [ht, hh] at heq
    exact ⟨e, he, (hq u).trans ht.symm, by lia⟩

/-- An arbitrary integer endpoint reached from a chosen lift is another chosen lift. -/
theorem exists_chosen_of_liftReach (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q)
    {u : Fin n} {z : ℤ}
    (h : Relation.ReflTransGen (D.liftStep θ.val) (q u) z) :
    ∃ v : Fin n, z = q v ∧ Relation.ReflTransGen (D.edgeData.selected θ.val) u v := by
  induction h with
  | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨v, rfl, hv⟩ := ih
    obtain ⟨e, he, hres, rfl⟩ := hs
    have ht : v = e.tail := (hq v).symm.trans hres
    have heq : q e.head - q e.tail = (e.length.val : ℤ) := hp e he
    refine ⟨e.head, ?_, hv.tail ⟨e, he, ht.symm, rfl⟩⟩
    rw [ht]
    lia

/-- Finite selected reachability lifts to the chosen integer positions. -/
theorem liftReach_of_selectedReach (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q)
    {u v : Fin n} (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    Relation.ReflTransGen (D.liftStep θ.val) (q u) (q v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ((θ.liftStep_chosen_iff hq hp).mpr hs)

/-- Full lifted reachability between chosen lifts equals finite selected reachability. -/
theorem liftReach_chosen_iff (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) {u v : Fin n} :
    Relation.ReflTransGen (D.liftStep θ.val) (q u) (q v) ↔
      Relation.ReflTransGen (D.edgeData.selected θ.val) u v := by
  constructor
  · intro h
    obtain ⟨w, hw, huw⟩ := θ.exists_chosen_of_liftReach hq hp h
    have hvw : v = w := D.injective_of_residue_section hq hw
    exact hvw.symm ▸ huw
  · exact θ.liftReach_of_selectedReach hq hp

/-- The full integer cover test is the finite reachability cover ordered by chosen lifts. -/
theorem liftCover_chosen_iff (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) {u v : Fin n} :
    D.liftCover θ.val (q u) (q v) ↔
      q u < q v ∧ Relation.ReflTransGen (D.edgeData.selected θ.val) u v ∧
        ∀ w : Fin n, q u < q w → q w < q v →
          ¬ (Relation.ReflTransGen (D.edgeData.selected θ.val) u w ∧
            Relation.ReflTransGen (D.edgeData.selected θ.val) w v) := by
  constructor
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, (θ.liftReach_chosen_iff hq hp).mp hreach, ?_⟩
    intro w huw hwv hpaths
    exact hcover (q w) huw hwv
      ⟨θ.liftReach_of_selectedReach hq hp hpaths.1,
        θ.liftReach_of_selectedReach hq hp hpaths.2⟩
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, θ.liftReach_of_selectedReach hq hp hreach, ?_⟩
    intro z huz hzv hpaths
    obtain ⟨w, rfl, huw⟩ := θ.exists_chosen_of_liftReach hq hp hpaths.1
    exact hcover w huz hzv ⟨huw, (θ.liftReach_chosen_iff hq hp).mp hpaths.2⟩

end VerticalStripLLT.Circular.Orientation

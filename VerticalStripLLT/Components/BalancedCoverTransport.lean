import VerticalStripLLT.Components.BalancedHRVTransport

/-!
# Cover transport through compatible chosen lifts

Canonical ranks balance every selected edge of a forward diagram. The full
integer-cover tests on that diagram therefore match the chosen-lift cover tests
after any selected-relation relabeling increasing in the chosen lift order.
-/

namespace VerticalStripLLT.Circular.Orientation

variable {n : ℕ} {D E : Diagram n}

/-- The canonical integer representatives balance every selection in a forward diagram. -/
theorem canonical_balancedPotential_of_forward (η : Orientation E)
    (hforward : ∀ e : Edge E.area, e.tail < e.head) :
    E.naturalGain.BalancedPotential (E.strict ∪ η.val) (fun i => (i.val : ℤ)) := by
  intro e _
  change (e.head.val : ℤ) - (e.tail.val : ℤ) = (e.length.val : ℤ)
  have h := (E.naturalLift_of_tail_lt_head e (hforward e)).2
  lia

/-- Canonical forward covers correspond to full integer covers at the compatible lifts. -/
theorem liftCover_iff_of_balanced_relabel (θ : Orientation D) (η : Orientation E)
    (hforward : ∀ e : Edge E.area, e.tail < e.head)
    {q : Fin n → ℤ} (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q)
    (σ : Fin n ≃ Fin n) (hmono : StrictMono (q ∘ σ))
    (hrel : ∀ i j, E.edgeData.selected η.val i j ↔
      D.edgeData.selected θ.val (σ i) (σ j)) (i j : Fin n) :
    E.liftCover η.val (i.val : ℤ) (j.val : ℤ) ↔
      D.liftCover θ.val (q (σ i)) (q (σ j)) := by
  rw [η.liftCover_chosen_iff (q := fun v => (v.val : ℤ))
      (fun v => residue_intCast_eq v) (η.canonical_balancedPotential_of_forward hforward),
    θ.liftCover_chosen_iff hq hp]
  constructor
  · rintro ⟨hij, hreach, hcover⟩
    have hij' : i < j := by exact_mod_cast hij
    refine ⟨hmono hij', (θ.selectedReach_relabel_iff η σ hrel).mp hreach, ?_⟩
    intro w hiw hwj hpaths
    have hiw' : i < σ.symm w := hmono.lt_iff_lt.mp (by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hiw)
    have hwj' : σ.symm w < j := hmono.lt_iff_lt.mp (by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hwj)
    apply hcover (σ.symm w) (by exact_mod_cast hiw') (by exact_mod_cast hwj')
    constructor
    · apply (θ.selectedReach_relabel_iff η σ hrel).mpr
      simpa only [Equiv.apply_symm_apply] using hpaths.1
    · apply (θ.selectedReach_relabel_iff η σ hrel).mpr
      simpa only [Equiv.apply_symm_apply] using hpaths.2
  · rintro ⟨hij, hreach, hcover⟩
    have hij' : i < j := hmono.lt_iff_lt.mp hij
    refine ⟨by exact_mod_cast hij', (θ.selectedReach_relabel_iff η σ hrel).mpr hreach, ?_⟩
    intro w hiw hwj hpaths
    have hiw' : i < w := by exact_mod_cast hiw
    have hwj' : w < j := by exact_mod_cast hwj
    apply hcover (σ w) (hmono hiw') (hmono hwj')
    exact ⟨(θ.selectedReach_relabel_iff η σ hrel).mp hpaths.1,
      (θ.selectedReach_relabel_iff η σ hrel).mp hpaths.2⟩

end VerticalStripLLT.Circular.Orientation

import VerticalStripLLT.Components.BalancedLiftReach
import VerticalStripLLT.Components.CircularBalancedFlip

/-! One choice of compatible lifts works throughout an entire balanced component. -/

namespace VerticalStripLLT.Circular

variable {n : ℕ} {D : Diagram n}

theorem balancedPotential_iff_of_flip {θ η : Orientation D} (p : Fin n → ℤ)
    (h : Flip D θ η) :
    D.naturalGain.BalancedPotential (D.strict ∪ θ.val) p ↔
      D.naturalGain.BalancedPotential (D.strict ∪ η.val) p := by
  rcases h with h | h
  · exact h.some.balancedPotential_iff p
  · exact (h.some.balancedPotential_iff p).symm

theorem balancedPotential_iff_of_reachable {θ η : Orientation D} (p : Fin n → ℤ)
    (h : Relation.ReflTransGen (Flip D) θ η) :
    D.naturalGain.BalancedPotential (D.strict ∪ θ.val) p ↔
      D.naturalGain.BalancedPotential (D.strict ∪ η.val) p := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (balancedPotential_iff_of_flip p hs)

/-- Componentwise translations used to choose residues never need to be chosen again. -/
theorem exists_common_balancedLifts (θ : Orientation D)
    (hθ : D.naturalGain.Balanced (D.strict ∪ θ.val)) :
    ∃ q : Fin n → ℤ, (∀ v, D.residue (q v) = v) ∧ Function.Injective q ∧
      ∀ η ∈ flipComponent D θ, D.naturalGain.BalancedPotential (D.strict ∪ η.val) q := by
  obtain ⟨q, hq, hp, hinj⟩ := D.exists_injective_balancedLifts hθ
  refine ⟨q, hq, hinj, ?_⟩
  intro η hη
  exact (balancedPotential_iff_of_reachable q (mem_flipComponent_iff.mp hη)).mp hp

end VerticalStripLLT.Circular

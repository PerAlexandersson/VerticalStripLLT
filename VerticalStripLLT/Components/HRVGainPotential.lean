import VerticalStripLLT.Components.GainPotential
import VerticalStripLLT.Circular.HRVPotential

/-!
# Circular HRV displacement as a least gain potential

Reverse each natural edge and assign its positive natural length as gain.
The least nonnegative feasible potential for the full selected edge set is
exactly the displacement to the highest reachable integer lift.
-/

namespace VerticalStripLLT.Circular

open scoped Classical

noncomputable section

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- Natural-length constraints run opposite to the selected circular edges. -/
abbrev reversedGain : Components.GainData (Fin n) (Edge D.area) where
  tail e := e.head
  head e := e.tail
  gain e := e.length.val

/-- A reversed feasible potential decreases after adding the integer lift coordinate. -/
theorem reversedGain_feasible_step_bound {A : Finset (Edge D.area)} {p : Fin n → ℕ}
    (hp : D.reversedGain.Feasible (D.strict ∪ A) p) {z w : ℤ}
    (h : D.liftStep A z w) :
    w + (p (D.residue w) : ℤ) ≤ z + (p (D.residue z) : ℤ) := by
  obtain ⟨e, he, hz, hw⟩ := h
  have hedge := hp e he
  change (p e.head : ℤ) + (e.length.val : ℤ) ≤ p e.tail at hedge
  rw [hw, D.residue_add_length e z hz, hz]
  lia

/-- The same bound holds along every actual lifted selected path. -/
theorem reversedGain_feasible_reach_bound {A : Finset (Edge D.area)} {p : Fin n → ℕ}
    (hp : D.reversedGain.Feasible (D.strict ∪ A) p) {z w : ℤ}
    (h : Relation.ReflTransGen (D.liftStep A) z w) :
    w + (p (D.residue w) : ℤ) ≤ z + (p (D.residue z) : ℤ) := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (D.reversedGain_feasible_step_bound hp hs).trans ih

end Diagram

namespace Orientation

variable {n : ℕ} {D : Diagram n}

/-- Nonnegative displacement from a residue representative to its actual highest lift. -/
def hrvDistance (θ : Orientation D) (u : Fin n) : ℕ :=
  (θ.liftedHRV (u.val : ℤ) - (u.val : ℤ)).toNat

@[simp]
theorem hrvDistance_coe (θ : Orientation D) (u : Fin n) :
    (θ.hrvDistance u : ℤ) = θ.liftedHRV (u.val : ℤ) - (u.val : ℤ) := by
  exact Int.toNat_of_nonneg (sub_nonneg.mpr (θ.le_liftedHRV (u.val : ℤ)))

/-- Periodicity makes the displacement depend only on the residue. -/
theorem liftedHRV_sub_eq_hrvDistance (θ : Orientation D) {z : ℤ} {u : Fin n}
    (hz : D.residue z = u) : θ.liftedHRV z - z = (θ.hrvDistance u : ℤ) := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period
    (hz.trans (residue_intCast_eq (D := D) u).symm)
  rw [hk, θ.liftedHRV_translate, θ.hrvDistance_coe]
  ring

/-- HRV displacement satisfies every selected natural-length constraint,
including the strict edges. -/
theorem hrvDistance_feasible (θ : Orientation D) :
    D.reversedGain.Feasible (D.strict ∪ θ.val) θ.hrvDistance := by
  intro e he
  have ht : D.residue (e.tail.val : ℤ) = e.tail := residue_intCast_eq e.tail
  have hstep : D.liftStep θ.val (e.tail.val : ℤ)
      ((e.tail.val : ℤ) + (e.length.val : ℤ)) := ⟨e, he, ht, rfl⟩
  have hle := θ.liftedHRV_le_of_step hstep
  have hhead := θ.liftedHRV_sub_eq_hrvDistance (D.residue_add_length e _ ht)
  have htail := θ.hrvDistance_coe e.tail
  change (θ.hrvDistance e.head : ℤ) + (e.length.val : ℤ) ≤ θ.hrvDistance e.tail
  lia

/-- Every feasible nonnegative potential bounds the actual HRV displacement. -/
theorem hrvDistance_le_of_feasible (θ : Orientation D) {p : Fin n → ℕ}
    (hp : D.reversedGain.Feasible (D.strict ∪ θ.val) p) (u : Fin n) :
    θ.hrvDistance u ≤ p u := by
  have hbound := D.reversedGain_feasible_reach_bound hp
    (θ.liftedHRV_reachable (u.val : ℤ))
  rw [residue_intCast_eq] at hbound
  have hnonneg := Int.natCast_nonneg (p (D.residue (θ.liftedHRV (u.val : ℤ))))
  have hdist := θ.hrvDistance_coe u
  have hle : (θ.hrvDistance u : ℤ) ≤ p u := by lia
  exact_mod_cast hle

/-- The actual circular HRV displacement is the least feasible reversed gain potential. -/
theorem hrvDistance_eq_potential (θ : Orientation D) :
    θ.hrvDistance = D.reversedGain.potential (D.strict ∪ θ.val) := by
  funext u
  apply le_antisymm
  · exact θ.hrvDistance_le_of_feasible
      (D.reversedGain.potential_feasible ⟨θ.hrvDistance, θ.hrvDistance_feasible⟩) u
  · exact D.reversedGain.potential_le θ.hrvDistance_feasible u

/-- The finite least potential reconstructs HRV on the entire integer cover. -/
theorem liftedHRV_eq_add_potential (θ : Orientation D) (z : ℤ) :
    θ.liftedHRV z = z +
      (D.reversedGain.potential (D.strict ∪ θ.val) (D.residue z) : ℤ) := by
  have h := θ.liftedHRV_sub_eq_hrvDistance (z := z) rfl
  rw [θ.hrvDistance_eq_potential] at h
  lia

end Orientation

end

end VerticalStripLLT.Circular

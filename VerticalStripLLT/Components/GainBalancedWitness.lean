import VerticalStripLLT.Components.GainContraction
import Mathlib.Data.Finset.Prod

/-!
# Positive signed-walk obstructions to balancedness

Each original edge has a forward copy and a reverse copy with negated gain.
Feasibility on both copies forces equality of the original potential difference.
Consequently an unbalanced finite selection has a positive closed walk, and
even a positive simple cycle, in this doubled graph. Edge instances are retained.
-/

namespace VerticalStripLLT.Components.GainData

open scoped Classical

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- The `true` copy is forward; the `false` copy reverses endpoints and gain. -/
abbrev doubled : GainData V (E × Bool) where
  tail e := if e.2 then G.tail e.1 else G.head e.1
  head e := if e.2 then G.head e.1 else G.tail e.1
  gain e := if e.2 then G.gain e.1 else -G.gain e.1

/-- Select both directed copies of each original edge instance. -/
def doubledSelection (F : Finset E) : Finset (E × Bool) :=
  F.product Finset.univ

@[simp]
theorem mem_doubledSelection {F : Finset E} {e : E} {b : Bool} :
    (e, b) ∈ doubledSelection F ↔ e ∈ F := by
  simp [doubledSelection]

/-- The two opposing inequalities force the exact original edge difference. -/
theorem balancedPotential_of_doubled_feasible {F : Finset E} {p : V → ℕ}
    (hp : G.doubled.Feasible (doubledSelection F) p) :
    G.BalancedPotential F (fun v => (p v : ℤ)) := by
  intro e he
  have hforward := hp (e, true) (mem_doubledSelection.mpr he)
  have hreverse := hp (e, false) (mem_doubledSelection.mpr he)
  change (p (G.tail e) : ℤ) + G.gain e ≤ p (G.head e) at hforward
  change (p (G.head e) : ℤ) + -G.gain e ≤ p (G.tail e) at hreverse
  change (p (G.head e) : ℤ) - p (G.tail e) = G.gain e
  lia

theorem balanced_of_doubled_feasible {F : Finset E} {p : V → ℕ}
    (hp : G.doubled.Feasible (doubledSelection F) p) : G.Balanced F :=
  ⟨fun v => (p v : ℤ), G.balancedPotential_of_doubled_feasible hp⟩

/-- Failure of balancedness obstructs the closed-walk feasibility criterion. -/
theorem not_doubled_closedWalksNonpos_of_not_balanced [Fintype V]
    {F : Finset E} (hF : ¬G.Balanced F) :
    ¬G.doubled.ClosedWalksNonpos (doubledSelection F) := by
  intro hclosed
  obtain ⟨p, hp⟩ := G.doubled.exists_feasible_of_closedWalksNonpos
    (doubledSelection F) hclosed
  exact hF (G.balanced_of_doubled_feasible hp)

/-- An unbalanced selection has a positive signed closed-walk witness. -/
theorem exists_positive_doubled_closedWalk [Fintype V]
    {F : Finset E} (hF : ¬G.Balanced F) :
    ∃ (v : V) (p : G.doubled.Walk (doubledSelection F) v v),
      0 < G.doubled.walkGain p := by
  have h := G.not_doubled_closedWalksNonpos_of_not_balanced hF
  simpa only [ClosedWalksNonpos, not_forall, not_le] using h

/-- The obstruction may be chosen without repeated vertices before closure. -/
theorem exists_positive_doubled_simpleCycle [Fintype V]
    {F : Finset E} (hF : ¬G.Balanced F) :
    ∃ (v : V) (p : G.doubled.Walk (doubledSelection F) v v),
      G.doubled.SimpleCycle p ∧ 0 < G.doubled.walkGain p := by
  have hn := G.not_doubled_closedWalksNonpos_of_not_balanced hF
  have hs : ¬G.doubled.SimpleCyclesNonpos (doubledSelection F) := by
    intro hsimple
    exact hn ((G.doubled.closedWalksNonpos_iff_simpleCyclesNonpos
      (doubledSelection F)).mpr hsimple)
  simp only [SimpleCyclesNonpos, not_forall, not_le] at hs
  obtain ⟨v, p, hp, hpos⟩ := hs
  exact ⟨v, p, hp, hpos⟩

end

end VerticalStripLLT.Components.GainData

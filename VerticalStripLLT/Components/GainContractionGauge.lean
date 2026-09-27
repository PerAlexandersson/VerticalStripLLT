import VerticalStripLLT.Components.GainContraction
import VerticalStripLLT.Components.GainGauge

/-! Contracted cycle conditions are independent of the balanced potential. -/

namespace VerticalStripLLT.Components.GainData

noncomputable section

variable {V E : Type*} (G : GainData V E)

theorem contraction_eq_shiftGains {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) :
    G.contraction F q =
      (G.contraction F p).shiftGains (G.blockPotentialDifference hp hq) := by
  unfold contraction shiftGains
  congr 1
  funext e
  have h := G.contraction_gain_change hp hq e
  dsimp [shiftGains]
  lia

/-- The negative-cycle test on a contraction does not depend on potential choice. -/
theorem contraction_simpleCyclesNegative_iff {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) (A : Finset E) :
    (G.contraction F q).SimpleCyclesNegative A ↔
      (G.contraction F p).SimpleCyclesNegative A := by
  rw [G.contraction_eq_shiftGains hp hq]
  exact (G.contraction F p).simpleCyclesNegative_shiftGains_iff _ A

theorem contraction_closedWalksNonpos_iff {F : Finset E} {p q : V → ℤ}
    (hp : G.BalancedPotential F p) (hq : G.BalancedPotential F q) (A : Finset E) :
    (G.contraction F q).ClosedWalksNonpos A ↔
      (G.contraction F p).ClosedWalksNonpos A := by
  rw [G.contraction_eq_shiftGains hp hq]
  exact (G.contraction F p).closedWalksNonpos_shiftGains_iff _ A

end

end VerticalStripLLT.Components.GainData

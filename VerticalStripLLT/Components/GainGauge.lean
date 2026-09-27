import VerticalStripLLT.Components.GainScaling

/-! Potential shifts preserve the gains of directed closed walks. -/

namespace VerticalStripLLT.Components.GainData

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- Change gains by a vertex potential, preserving all edge instances and endpoints. -/
abbrev shiftGains (z : V → ℤ) : GainData V E where
  tail := G.tail
  head := G.head
  gain e := G.gain e - (z (G.head e) - z (G.tail e))

theorem walkGain_shiftGains (z : V → ℤ) {A : Finset E} {u v : V}
    (p : G.Walk A u v) :
    (G.shiftGains z).walkGain p = G.walkGain p - (z v - z u) := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => simp [walkGain]
  | @cons b c p e ih =>
    simp only [walkGain, Quiver.Path.addWeight_cons] at ih ⊢
    rw [ih]
    change G.walkGain p - (z b - z u) +
      (G.gain e.val - (z (G.head e.val) - z (G.tail e.val))) = _
    rw [e.property.2.1, e.property.2.2]
    change G.walkGain p - (z b - z u) + (G.gain e.val - (z c - z b)) =
      G.walkGain p + G.gain e.val - (z c - z u)
    lia

@[simp]
theorem closedWalkGain_shiftGains (z : V → ℤ) {A : Finset E} {v : V}
    (p : G.Walk A v v) : (G.shiftGains z).walkGain p = G.walkGain p := by
  simp only [G.walkGain_shiftGains, sub_self, sub_zero]

theorem closedWalksNonpos_shiftGains_iff (z : V → ℤ) (A : Finset E) :
    (G.shiftGains z).ClosedWalksNonpos A ↔ G.ClosedWalksNonpos A := by
  simp only [ClosedWalksNonpos, G.closedWalkGain_shiftGains]

theorem simpleCyclesNegative_shiftGains_iff (z : V → ℤ) (A : Finset E) :
    (G.shiftGains z).SimpleCyclesNegative A ↔ G.SimpleCyclesNegative A := by
  simp only [SimpleCyclesNegative, G.closedWalkGain_shiftGains]
  rfl

/-- Strict negativity extends from simple cycles to every nonempty closed walk. -/
theorem walkGain_neg_of_simpleCyclesNegative [Fintype V] {A : Finset E}
    (h : G.SimpleCyclesNegative A) {v : V} (p : G.Walk A v v)
    (hp : 0 < G.walkLength p) : G.walkGain p < 0 := by
  have hscale := (G.closedWalksNonpos_strictScale_iff A (Fintype.card V) le_rfl).mpr h
  have hbound := hscale v p
  rw [G.walkGain_strictScale] at hbound
  have hlen : (0 : ℤ) < G.walkLength p := by exact_mod_cast hp
  by_contra hn
  have hg : 0 ≤ G.walkGain p := by lia
  have hmul := mul_nonneg (Int.natCast_nonneg (Fintype.card V)) hg
  lia

end

end VerticalStripLLT.Components.GainData

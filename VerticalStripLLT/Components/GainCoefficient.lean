import VerticalStripLLT.Components.GainContractionGauge
import VerticalStripLLT.Components.GainContractionConnectivity

/-! Potential-independent signed coefficients for balanced edge subsets. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open Classical OrderedPartitions

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

/-- The contracted cycle conditions, with existence of a compatible integer potential. -/
def ContractedGood (X F : Finset E) : Prop :=
  ∃ p : V → ℤ, G.BalancedPotential F p ∧
    (G.contraction F p).SimpleCyclesNegative (X \ F) ∧
    TotallyCyclic ((G.contraction F p).selectedRelation (X \ F))

theorem contractedGood_iff {X F : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) :
    G.ContractedGood X F ↔
      (G.contraction F p).SimpleCyclesNegative (X \ F) ∧
        TotallyCyclic ((G.contraction F p).selectedRelation (X \ F)) := by
  constructor
  · rintro ⟨q, hq, hn, ht⟩
    exact ⟨(G.contraction_simpleCyclesNegative_iff hp hq _).mp hn, ht⟩
  · rintro ⟨hn, ht⟩
    exact ⟨p, hp, hn, ht⟩

/-- The companion coefficient; the sum exponent equals the difference exponent
when `F ⊆ X`. The sum form keeps finite-sum sign calculations over natural powers. -/
def coefficient (X F : Finset E) : ℤ :=
  if F ⊆ X ∧ G.ContractedGood X F then
    (-1) ^ (weakComponentCount (G.selectedRelation F) +
      weakComponentCount (G.selectedRelation X))
  else 0

theorem coefficient_eq_zero_of_not_subset {X F : Finset E} (h : ¬F ⊆ X) :
    G.coefficient X F = 0 := by
  simp [coefficient, h]

theorem coefficient_eq_zero_of_not_balanced {X F : Finset E} (h : ¬G.Balanced F) :
    G.coefficient X F = 0 := by
  have hg : ¬G.ContractedGood X F := fun ⟨p, hp, _, _⟩ => h ⟨p, hp⟩
  simp [coefficient, hg]

theorem coefficient_eq_fixed_potential {X F : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) :
    G.coefficient X F =
      if F ⊆ X ∧ (G.contraction F p).SimpleCyclesNegative (X \ F) ∧
          TotallyCyclic ((G.contraction F p).selectedRelation (X \ F)) then
        (-1) ^ (weakComponentCount (G.selectedRelation F) +
          weakComponentCount (G.selectedRelation X))
      else 0 := by
  rw [coefficient, G.contractedGood_iff hp]
  split_ifs <;> rfl

/-- A fixed-potential coefficient separates the constant contracted-vertex sign. -/
theorem coefficient_eq_contraction {X F : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) (hFX : F ⊆ X) :
    G.coefficient X F = (-1 : ℤ) ^ weakComponentCount (G.selectedRelation F) *
      (if (G.contraction F p).SimpleCyclesNegative (X \ F) ∧
          TotallyCyclic ((G.contraction F p).selectedRelation (X \ F))
       then (-1 : ℤ) ^ weakComponentCount ((G.contraction F p).selectedRelation (X \ F))
       else 0) := by
  rw [G.coefficient_eq_fixed_potential hp,
    G.contraction_weakComponentCount p hFX]
  simp only [hFX, true_and]
  split_ifs <;> simp [pow_add]

/-- The sum-exponent definition has exactly the sign in the finite companion. -/
theorem coefficient_eq_difference_sign [Fintype V] {X F : Finset E} (hFX : F ⊆ X) :
    G.coefficient X F =
      if G.ContractedGood X F then
        (-1 : ℤ) ^ (weakComponentCount (G.selectedRelation F) -
          weakComponentCount (G.selectedRelation X))
      else 0 := by
  have hle := G.weakComponentCount_le_of_subset hFX
  have hsign : (-1 : ℤ) ^ (weakComponentCount (G.selectedRelation F) +
      weakComponentCount (G.selectedRelation X)) =
      (-1 : ℤ) ^ (weakComponentCount (G.selectedRelation F) -
        weakComponentCount (G.selectedRelation X)) := by
    conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    lia
  simp only [coefficient, hFX, true_and, hsign]

end

end VerticalStripLLT.Components.GainData

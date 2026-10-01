import VerticalStripLLT.Components.GainCoefficient
import VerticalStripLLT.Components.GainZeroCycles

/-! The companion coefficients reduce to the delta function on a balanced graph. -/

namespace VerticalStripLLT.Components.GainData

open Classical OrderedPartitions

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq E] (G : GainData V E)

omit [DecidableEq E] in
theorem simpleCyclesNegative_empty : G.SimpleCyclesNegative ∅ := by
  apply (G.exists_feasible_strictScale_iff ∅ (Fintype.card V) le_rfl).mp
  exact ⟨fun _ => 0, by intro e he; simp at he⟩

omit [Fintype V] [DecidableEq E] in
theorem totallyCyclic_selectedRelation_empty : TotallyCyclic (G.selectedRelation ∅) := by
  rintro x y ⟨e, he, _⟩
  simp at he

/-- A balanced graph has coefficient one on itself. -/
theorem coefficient_self {F : Finset E} (hF : G.Balanced F) : G.coefficient F F = 1 := by
  obtain ⟨p, hp⟩ := hF
  rw [G.coefficient_eq_difference_sign (X := F) (F := F) (by rfl)]
  have hg : G.ContractedGood F F := by
    refine (G.contractedGood_iff hp).mpr ?_
    simp only [Finset.sdiff_self]
    exact ⟨(G.contraction F p).simpleCyclesNegative_empty,
      (G.contraction F p).totallyCyclic_selectedRelation_empty⟩
  simp [hg]

/-- No proper subset is good when the original selected graph is balanced. -/
theorem eq_of_contractedGood_of_balanced {X F : Finset E}
    (hX : G.Balanced X) (hFX : F ⊆ X) (hg : G.ContractedGood X F) : F = X := by
  obtain ⟨p, hp⟩ := hX
  have hpF : G.BalancedPotential F p := BalancedPotential.mono G hp hFX
  obtain ⟨hn, ht⟩ := (G.contractedGood_iff hpF).mp hg
  have hz : ∀ e ∈ X \ F, (G.contraction F p).gain e = 0 := by
    intro e he
    change G.gain e - (p (G.head e) - p (G.tail e)) = 0
    rw [hp e (Finset.mem_sdiff.mp he).1, sub_self]
  have hempty := (G.contraction F p).eq_empty_of_zeroGain_simpleNegative_totallyCyclic
    (X \ F) hz hn ht
  exact Finset.Subset.antisymm hFX (Finset.sdiff_eq_empty_iff_subset.mp hempty)

/-- The balanced base case, including unsupported and unbalanced subsets. -/
theorem coefficient_eq_delta_of_balanced {X : Finset E} (hX : G.Balanced X)
    (F : Finset E) : G.coefficient X F = if F = X then 1 else 0 := by
  by_cases h : F = X
  · subst F
    simp [G.coefficient_self hX]
  · have hbad : ¬(F ⊆ X ∧ G.ContractedGood X F) := by
      rintro ⟨hFX, hg⟩
      exact h (G.eq_of_contractedGood_of_balanced hX hFX hg)
    simp [coefficient, hbad, h]

end

end VerticalStripLLT.Components.GainData

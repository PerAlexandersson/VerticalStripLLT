import VerticalStripLLT.Components.WeightedToggleCancellation
import VerticalStripLLT.Components.GainExcess

/-! Signed cancellation preserves the complete least-potential vector. -/

namespace VerticalStripLLT.Components.GainData

open Classical
open scoped BigOperators

noncomputable section

variable {V E M : Type*} [DecidableEq E] [AddCommGroup M] (G : GainData V E)

/-- Any value of the actual least potential has the same signed cancellation. -/
theorem sum_powerset_potential_value_eq_zero (A N : Finset E) (value : (V → ℕ) → M)
    (hslack : ∀ J ⊆ N, (∃ p, G.Feasible (A ∪ J) p) →
      (G.slackEdges N (G.potential (A ∪ J))).Nonempty) :
    (∑ J ∈ N.powerset, if ∃ p, G.Feasible (A ∪ J) p
      then ((-1 : ℤ) ^ J.card) • value (G.potential (A ∪ J)) else 0) = 0 := by
  by_cases hE : Nonempty E
  · let fallback : E := Classical.choice hE
    let e (J : Finset E) := G.slackChoice N fallback (G.potential (A ∪ J))
    have hmem (J : Finset E) (hJ : J ∈ N.powerset)
        (hgood : ∃ p, G.Feasible (A ∪ J) p) :
        e J ∈ N ∧ (G.potential (A ∪ J) (G.tail (e J)) : ℤ) + G.gain (e J) <
          G.potential (A ∪ J) (G.head (e J)) := by
      exact Finset.mem_filter.mp
        (G.slackChoice_mem (fallback := fallback)
          (hslack J (Finset.mem_powerset.mp hJ) hgood))
    apply sum_powerset_good_toggle_weighted_eq_zero N
      (fun J => ∃ p, G.Feasible (A ∪ J) p) e
      (fun J => value (G.potential (A ∪ J)))
    · intro J hJ hgood
      exact (hmem J hJ hgood).1
    · intro J hJ hgood
      exact (G.potential_union_toggle_eq hgood (hmem J hJ hgood).2).1
    · intro J hJ hgood
      have hp := (G.potential_union_toggle_eq hgood (hmem J hJ hgood).2).2
      change G.slackChoice N fallback (G.potential (A ∪ toggleSubset e J)) = _
      rw [show G.potential (A ∪ toggleSubset e J) = G.potential (A ∪ J) from hp]
    · intro J hJ hgood
      have hp := (G.potential_union_toggle_eq hgood (hmem J hJ hgood).2).2
      exact congrArg value hp
  · apply Finset.sum_eq_zero
    intro J hJ
    have hbad : ¬∃ p, G.Feasible (A ∪ J) p := by
      intro hgood
      obtain ⟨e, _⟩ := hslack J (Finset.mem_powerset.mp hJ) hgood
      exact hE ⟨e⟩
    simp [hbad]

/-- The gain-excess recurrence before any evaluation of the complete potential vector. -/
theorem sum_powerset_potential_value_eq_zero_of_gain_excess
    (A N : Finset E) (P Nsteps : List E) (value : (V → ℕ) → M)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset, if ∃ p, G.Feasible (A ∪ J) p
      then ((-1 : ℤ) ^ J.card) • value (G.potential (A ∪ J)) else 0) = 0 := by
  apply G.sum_powerset_potential_value_eq_zero A N value
  intro J _ hgood
  obtain ⟨e, he, hs⟩ := G.exists_slack_of_gain_excess
    (fun e he => Finset.mem_union_left J (hP e he))
    (G.potential_feasible hgood) hperm hexcess
  exact ⟨e, Finset.mem_filter.mpr ⟨hN e he, hs⟩⟩

end

end VerticalStripLLT.Components.GainData

import VerticalStripLLT.Components.GainLevels
import VerticalStripLLT.Components.PartitionLevels
import VerticalStripLLT.Components.PartitionConnectivity

/-! The signed coefficient cancellation in the contracted finite gain graph. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical OrderedPartitions

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] (G : GainData V E)

/-- The selected relation forgets edge multiplicity only for connectivity and levels. -/
def selectedRelation (A : Finset E) (x y : V) : Prop :=
  ∃ e ∈ A, G.tail e = x ∧ G.head e = y

theorem compatible_iff_levelCompatible (A : Finset E) (bs : List (Finset V))
    (hbs : IsCompatible (fun _ _ : V => False) Finset.univ bs) :
    IsCompatible (G.selectedRelation A) Finset.univ bs ↔
      G.LevelCompatible (blockLevel bs) A := by
  rw [compatible_iff_blockLevel _ hbs]
  constructor
  · intro h e he
    exact h _ (Finset.mem_univ _) _ (Finset.mem_univ _) ⟨e, he, rfl, rfl⟩
  · rintro h x _ y _ ⟨e, he, rfl, rfl⟩
    exact h e he

theorem signedSum_eq_level_sum (A : Finset E) :
    signedSum (G.selectedRelation A) Finset.univ =
      ∑ bs ∈ partitions (fun _ _ : V => False) Finset.univ,
        if G.LevelCompatible (blockLevel bs) A then (-1 : ℤ) ^ bs.length else 0 := by
  rw [signedSum, partitions_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro bs hbs
  rw [G.compatible_iff_levelCompatible A bs ((mem_partitions _ _ _).mp hbs)]

/-- Swap the finite partition and edge-selection sums, then cancel each level assignment. -/
theorem sum_powerset_signedPartitions_eq_zero_of_gain_excess
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hcover : ∀ e ∈ N, e ∈ Nsteps)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset, (-1 : ℤ) ^ J.card *
      (if G.SimpleCyclesNegative (A ∪ J)
       then signedSum (G.selectedRelation (A ∪ J)) Finset.univ else 0)) = 0 := by
  have hterm (J : Finset E) :
      (-1 : ℤ) ^ J.card * (if G.SimpleCyclesNegative (A ∪ J)
        then signedSum (G.selectedRelation (A ∪ J)) Finset.univ else 0) =
      ∑ bs ∈ partitions (fun _ _ : V => False) Finset.univ,
        (-1 : ℤ) ^ bs.length *
          (if G.LevelCompatible (blockLevel bs) (A ∪ J) ∧
            G.SimpleCyclesNegative (A ∪ J) then (-1 : ℤ) ^ J.card else 0) := by
    rw [G.signedSum_eq_level_sum]
    by_cases hn : G.SimpleCyclesNegative (A ∪ J)
    · simp only [hn, and_true, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro bs hbs
      split_ifs <;> ring
    · simp [hn]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro bs hbs
  rw [← Finset.mul_sum,
    G.sum_powerset_level_negative_eq_zero_of_gain_excess A N P Nsteps
      (blockLevel bs) hN hcover hP hperm hexcess, mul_zero]

/-- The companion coefficient identity, with the actual weak-component sign
and both negative-cycle and total-cyclicity conditions. -/
theorem sum_powerset_cyclicNegative_eq_zero_of_gain_excess
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hcover : ∀ e ∈ N, e ∈ Nsteps)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset,
      if G.SimpleCyclesNegative (A ∪ J) ∧ TotallyCyclic (G.selectedRelation (A ∪ J))
      then (-1 : ℤ) ^ (J.card + weakComponentCount (G.selectedRelation (A ∪ J)))
      else 0) = 0 := by
  have h := G.sum_powerset_signedPartitions_eq_zero_of_gain_excess
    A N P Nsteps hN hcover hP hperm hexcess
  simp_rw [signedSum_eq_weakComponentCount] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp_all [pow_add]

end

end VerticalStripLLT.Components.GainData

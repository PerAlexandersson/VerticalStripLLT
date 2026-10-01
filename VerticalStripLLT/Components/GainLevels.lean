import VerticalStripLLT.Components.GainNegativeCancellation

/-! A strictly upward edge preserves feasibility and cancels compatible selections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

/-- Every selected edge is nondecreasing in the finite level assignment. -/
def LevelCompatible (level : V → ℕ) (A : Finset E) : Prop :=
  ∀ e ∈ A, level (G.tail e) ≤ level (G.head e)

/-- Raising successive levels sufficiently far apart accommodates an upward edge. -/
theorem exists_feasible_insert_of_level_lt {A : Finset E} {e : E} {level : V → ℕ}
    (hlevel : G.LevelCompatible level A)
    (he : level (G.tail e) < level (G.head e))
    (hfeas : ∃ p, G.Feasible A p) : ∃ p, G.Feasible (insert e A) p := by
  obtain ⟨p, hp⟩ := hfeas
  let K : ℕ := p (G.tail e) + (G.gain e).toNat + 1
  have hK : (p (G.tail e) : ℤ) + G.gain e ≤ K := by
    have h : G.gain e ≤ ((G.gain e).toNat : ℤ) := Int.self_le_toNat (G.gain e)
    dsimp [K]
    lia
  refine ⟨fun v => p v + K * level v, ?_⟩
  intro f hf
  simp only [Int.natCast_add, Int.natCast_mul]
  rcases Finset.mem_insert.mp hf with rfl | hf
  · have hlevels : (level (G.tail f) : ℤ) + 1 ≤ level (G.head f) := by
      exact_mod_cast he
    have hmul := mul_le_mul_of_nonneg_left hlevels (Int.natCast_nonneg K)
    have hphead := Int.natCast_nonneg (p (G.head f))
    nlinarith
  · have hlevels : (level (G.tail f) : ℤ) ≤ level (G.head f) := by
      exact_mod_cast hlevel f hf
    have hmul := mul_le_mul_of_nonneg_left hlevels (Int.natCast_nonneg K)
    have hpf := hp f hf
    linarith

/-- Inserting a strictly upward edge cannot create a bad directed cycle. -/
theorem simpleCyclesNegative_insert_of_level_lt [Fintype V]
    {A : Finset E} {e : E} {level : V → ℕ}
    (hlevel : G.LevelCompatible level A)
    (he : level (G.tail e) < level (G.head e))
    (hneg : G.SimpleCyclesNegative A) : G.SimpleCyclesNegative (insert e A) := by
  let M := Fintype.card V
  apply (G.exists_feasible_strictScale_iff (insert e A) M le_rfl).mp
  apply (G.strictScale M).exists_feasible_insert_of_level_lt hlevel he
  exact (G.exists_feasible_strictScale_iff A M le_rfl).mpr hneg

/-- The strictly upward optional-edge case of the ordered-partition cancellation. -/
theorem sum_powerset_level_negative_eq_zero_of_upward [Fintype V]
    (A N : Finset E) (level : V → ℕ) (e : E) (heN : e ∈ N)
    (he : level (G.tail e) < level (G.head e)) :
    (∑ J ∈ N.powerset,
      if G.LevelCompatible level (A ∪ J) ∧ G.SimpleCyclesNegative (A ∪ J)
      then (-1 : ℤ) ^ J.card else 0) = 0 := by
  convert sum_powerset_good_toggle_eq_zero N
    (fun J => G.LevelCompatible level (A ∪ J) ∧ G.SimpleCyclesNegative (A ∪ J))
    (fun _ => e) ?_ ?_ ?_ using 1
  · apply Finset.sum_congr rfl
    intro J hJ
    split_ifs <;> rfl
  · intro J hJ hgood
    exact heN
  · intro J hJ hgood
    unfold toggleSubset
    dsimp only
    split_ifs with heJ
    · have hsub : A ∪ J.erase e ⊆ A ∪ J := by
        exact Finset.union_subset_union_right (Finset.erase_subset _ _)
      refine ⟨fun f hf => hgood.1 f (hsub hf), ?_⟩
      let M := Fintype.card V
      apply (G.exists_feasible_strictScale_iff _ M le_rfl).mp
      obtain ⟨p, hp⟩ := (G.exists_feasible_strictScale_iff _ M le_rfl).mpr hgood.2
      exact ⟨p, (G.strictScale M).feasible_mono hsub hp⟩
    · have hset : A ∪ insert e J = insert e (A ∪ J) := by ext; simp
      rw [hset]
      refine ⟨?_, G.simpleCyclesNegative_insert_of_level_lt hgood.1 he hgood.2⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he.le
      · exact hgood.1 f hf
  · intro J hJ hgood
    rfl

omit [DecidableEq E] in
/-- Balanced endpoints force all backward steps to stay in one level when
the forward steps rise and no backward edge rises in its own direction. -/
theorem backward_levels_eq_of_endpoint_balance {P Nsteps : List E} {level : V → ℕ}
    (hP : ∀ e ∈ P, level (G.tail e) ≤ level (G.head e))
    (hN : ∀ e ∈ Nsteps, level (G.head e) ≤ level (G.tail e))
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head)) :
    ∀ e ∈ Nsteps, level (G.tail e) = level (G.head e) := by
  have hbal := (hperm.map level).sum_eq
  simp only [List.map_append, List.map_map, List.sum_append, Function.comp_def] at hbal
  have hPle := List.sum_le_sum hP
  intro e he
  by_contra hne
  have hstrict : level (G.head e) < level (G.tail e) :=
    lt_of_le_of_ne (hN e he) (Ne.symm hne)
  have hNlt := List.sum_lt_sum (fun e => level (G.head e))
    (fun e => level (G.tail e)) hN ⟨e, he, hstrict⟩
  lia

/-- Every fixed level assignment has a zero signed negative-cycle sum in the
presence of the companion's closed excess walk. -/
theorem sum_powerset_level_negative_eq_zero_of_gain_excess [Fintype V]
    (A N : Finset E) (P Nsteps : List E) (level : V → ℕ)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hcover : ∀ e ∈ N, e ∈ Nsteps)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset,
      if G.LevelCompatible level (A ∪ J) ∧ G.SimpleCyclesNegative (A ∪ J)
      then (-1 : ℤ) ^ J.card else 0) = 0 := by
  by_cases hA : G.LevelCompatible level A
  · by_cases hup : ∃ e ∈ N, level (G.tail e) < level (G.head e)
    · obtain ⟨e, heN, he⟩ := hup
      exact G.sum_powerset_level_negative_eq_zero_of_upward A N level e heN he
    · have hflat := G.backward_levels_eq_of_endpoint_balance
        (fun e he => hA e (hP e he))
        (fun e he => le_of_not_gt (fun h => hup ⟨e, hN e he, h⟩)) hperm
      have hcomp (J : Finset E) (hJ : J ⊆ N) : G.LevelCompatible level (A ∪ J) := by
        intro e he
        rcases Finset.mem_union.mp he with he | he
        · exact hA e he
        · exact (hflat e (hcover e (hJ he))).le
      calc
        _ = ∑ J ∈ N.powerset,
            if G.SimpleCyclesNegative (A ∪ J) then (-1 : ℤ) ^ J.card else 0 := by
          apply Finset.sum_congr rfl
          intro J hJ
          simp only [hcomp J (Finset.mem_powerset.mp hJ), true_and]
        _ = 0 := G.sum_powerset_simpleCyclesNegative_eq_zero_of_gain_excess
          A N P Nsteps hN hP hperm hexcess
  · apply Finset.sum_eq_zero
    intro J hJ
    have hbad : ¬G.LevelCompatible level (A ∪ J) := by
      intro h
      exact hA (fun e he => h e (Finset.mem_union_left J he))
    simp only [hbad, false_and, ite_false]

end

end VerticalStripLLT.Components.GainData

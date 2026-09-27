import VerticalStripLLT.Components.GainPotential
import VerticalStripLLT.Components.GainCancellation

/-! Signed feasibility cancellation using the least-potential slack pivot. -/

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

/-- Optional constraints that are strictly slack at the canonical potential. -/
def slackEdges (N : Finset E) (p : V → ℕ) : Finset E :=
  N.filter (fun e => (p (G.tail e) : ℤ) + G.gain e < p (G.head e))

private def slackChoice (N : Finset E) (fallback : E) (p : V → ℕ) : E :=
  if h : (G.slackEdges N p).Nonempty then h.choose else fallback

omit [DecidableEq E] in
private theorem slackChoice_mem {N : Finset E} {fallback : E} {p : V → ℕ}
    (h : (G.slackEdges N p).Nonempty) :
    G.slackChoice N fallback p ∈ G.slackEdges N p := by
  simp only [slackChoice, dite_eq_left h]
  exact h.choose_spec

/-- A slack optional edge can be toggled while preserving feasibility and the
canonical potential, even if it is also a required edge. -/
theorem potential_union_toggle_eq {A J : Finset E} {e : E}
    (hA : ∃ p, G.Feasible (A ∪ J) p)
    (hslack : (G.potential (A ∪ J) (G.tail e) : ℤ) + G.gain e <
      G.potential (A ∪ J) (G.head e)) :
    let J' := if e ∈ J then J.erase e else insert e J
    (∃ p, G.Feasible (A ∪ J') p) ∧ G.potential (A ∪ J') = G.potential (A ∪ J) := by
  dsimp
  split_ifs with he
  · have hsub : A ∪ J.erase e ⊆ A ∪ J := by
      intro f hf
      grind
    refine ⟨⟨_, G.feasible_mono hsub (G.potential_feasible hA)⟩, ?_⟩
    by_cases heA : e ∈ A
    · rw [Finset.union_erase_of_mem heA]
    · have hset : A ∪ J.erase e = (A ∪ J).erase e := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem heA]
      rw [hset]
      exact G.potential_erase_eq hA hslack
  · have hset : A ∪ insert e J = insert e (A ∪ J) := by ext; simp
    rw [hset]
    have hp : G.Feasible (insert e (A ∪ J)) (G.potential (A ∪ J)) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact le_of_lt hslack
      · exact G.potential_feasible hA f hf
    exact ⟨⟨_, hp⟩, G.potential_insert_eq hA (le_of_lt hslack)⟩

/-- If every feasible selection has a slack optional constraint, the signed
sum of its feasible subsets vanishes. The pivot is determined by the actual
canonical potential, so its invariance is proved rather than assumed. -/
theorem sum_powerset_feasible_eq_zero (A N : Finset E)
    (hslack : ∀ J ⊆ N, (∃ p, G.Feasible (A ∪ J) p) →
      (G.slackEdges N (G.potential (A ∪ J))).Nonempty) :
    (∑ J ∈ N.powerset, if ∃ p, G.Feasible (A ∪ J) p then (-1 : ℤ) ^ J.card else 0) =
      0 := by
  by_cases hE : Nonempty E
  · let fallback : E := Classical.choice hE
    let e (J : Finset E) := G.slackChoice N fallback (G.potential (A ∪ J))
    have hmem (J : Finset E) (hJ : J ∈ N.powerset)
        (hgood : ∃ p, G.Feasible (A ∪ J) p) :
        e J ∈ N ∧ (G.potential (A ∪ J) (G.tail (e J)) : ℤ) + G.gain (e J) <
          G.potential (A ∪ J) (G.head (e J)) := by
      exact Finset.mem_filter.mp
        (G.slackChoice_mem (fallback := fallback) (hslack J (Finset.mem_powerset.mp hJ)
          hgood))
    apply sum_powerset_good_toggle_eq_zero N (fun J => ∃ p, G.Feasible (A ∪ J) p) e
    · intro J hJ hgood
      exact (hmem J hJ hgood).1
    · intro J hJ hgood
      exact (G.potential_union_toggle_eq hgood (hmem J hJ hgood).2).1
    · intro J hJ hgood
      have hp := (G.potential_union_toggle_eq hgood (hmem J hJ hgood).2).2
      change G.slackChoice N fallback (G.potential (A ∪ toggleSubset e J)) = _
      rw [show G.potential (A ∪ toggleSubset e J) = G.potential (A ∪ J) from hp]
  · have hbad (J : Finset E) (hJ : J ∈ N.powerset) :
        ¬∃ p, G.Feasible (A ∪ J) p := by
      intro hgood
      obtain ⟨e, _⟩ := hslack J (Finset.mem_powerset.mp hJ) hgood
      exact hE ⟨e⟩
    apply Finset.sum_eq_zero
    intro J hJ
    simp [hbad J hJ]

end

end VerticalStripLLT.Components.GainData

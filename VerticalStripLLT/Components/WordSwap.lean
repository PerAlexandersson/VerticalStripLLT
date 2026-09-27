import VerticalStripLLT.Components.BlockExtractor

/-! Compatibility under a contextual adjacent swap. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*}

/-- Swapping adjacent letters changes compatibility only by their internal edge.

The hypothesis is the compatibility condition for the order `a,b`; all
relations involving either letter and the fixed context occur on both sides.
-/
theorem wordCompatible_adjacent_swap_iff
    (R : V → V → Prop) (ρ σ : List V) (a b : V) (hba : ¬ R b a) :
    wordCompatible R (ρ ++ [b, a] ++ σ) ↔
      wordCompatible R (ρ ++ [a, b] ++ σ) ∧ ¬ R a b := by
  simp [wordCompatible, List.pairwise_append, List.pairwise_cons, hba,
    and_assoc, and_left_comm, and_comm]

variable [LinearOrder V]

/-- The `acb`/`cab` specialization under a forward relation. -/
theorem wordCompatible_acb_cab_iff
    (R : V → V → Prop) (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (ρ σ : List V) {a b c : V} (hab : a < b) (hbc : b < c) :
    wordCompatible R (ρ ++ [c, a, b] ++ σ) ↔
      wordCompatible R (ρ ++ [a, c, b] ++ σ) ∧ ¬ R a c := by
  simpa [List.append_assoc] using
    (wordCompatible_adjacent_swap_iff R ρ ([b] ++ σ) a c (by
      intro hca
      exact (not_lt_of_ge (le_of_lt (lt_trans hab hbc))) (hforward hca)))

/-- The `bac`/`bca` specialization under a forward relation. -/
theorem wordCompatible_bac_bca_iff
    (R : V → V → Prop) (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (ρ σ : List V) {a b c : V} (hab : a < b) (hbc : b < c) :
    wordCompatible R (ρ ++ [b, c, a] ++ σ) ↔
      wordCompatible R (ρ ++ [b, a, c] ++ σ) ∧ ¬ R a c := by
  simpa [List.append_assoc] using
    (wordCompatible_adjacent_swap_iff R (ρ ++ [b]) σ a c (by
      intro hca
      exact (not_lt_of_ge (le_of_lt (lt_trans hab hbc))) (hforward hca)))

/-- Exchange the selected short edge `a,b` for `b,c` in a compatible word.

The `Nodup` hypothesis keeps the three displayed letters out of the exterior
context, which is needed because the exchanged relation is global.
-/
theorem wordCompatible_exchange_of_nodup
    (R S : V → V → Prop)
    {a b c : V}
    (hS : ∀ u v, S u v ↔
      (u = b ∧ v = c) ∨ (R u v ∧ ¬ (u = a ∧ v = b)))
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (ρ σ : List V) (hab : a < b) (hbc : b < c)
    (hw : (ρ ++ [a, c, b] ++ σ).Nodup)
    (hcompat : wordCompatible R (ρ ++ [a, c, b] ++ σ)) :
    wordCompatible S (ρ ++ [b, a, c] ++ σ) := by
  have hρ : wordCompatible S ρ := by
    have hp := (List.pairwise_append.mp (List.pairwise_append.mp hcompat).1).1
    apply hp.imp_of_mem
    intro x y hx hy hR hS'
    rcases (hS y x).mp hS' with hnew | hold
    · have hn := (List.nodup_append.mp hw).1
      have hdis := (List.nodup_append.mp hn).2.2
      exact hdis y hy b (by simp) hnew.1
    · exact hR hold.1
  have hσ : wordCompatible S σ := by
    have hp := (List.pairwise_append.mp hcompat).2.1
    apply hp.imp_of_mem
    intro x y hx hy hR hS'
    rcases (hS y x).mp hS' with hnew | hold
    · have hdis := (List.nodup_append.mp hw).2.2
      exact hdis b (by simp) y hy hnew.1.symm
    · exact hR hold.1
  simp [wordCompatible, List.pairwise_append, List.pairwise_cons,
    List.nodup_append, List.nodup_cons] at hw hcompat
  simp only [wordCompatible, List.pairwise_append]
  refine ⟨⟨hρ, ?_, ?_⟩, hσ, ?_⟩
  all_goals simp [List.pairwise_cons, hS]; grind

end

end VerticalStripLLT.Components

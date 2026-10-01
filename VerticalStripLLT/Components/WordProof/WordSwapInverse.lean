import VerticalStripLLT.Components.WordProof.BlockExtractor

/-! The inverse short-edge exchange for compatible words. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- Exchange `b,c` for `a,b` when the source word is `bac`.

The `Nodup` hypothesis keeps the exchanged letters out of the exterior
context, so the displayed relation exchange is global without creating a new
exterior obstruction.
-/
theorem wordCompatible_exchange_inverse_of_nodup
    (R S : V → V → Prop)
    {a b c : V}
    (hS : ∀ u v, S u v ↔
      (u = a ∧ v = b) ∨ (R u v ∧ ¬ (u = b ∧ v = c)))
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (ρ σ : List V) (hab : a < b) (hbc : b < c)
    (hw : (ρ ++ [b, a, c] ++ σ).Nodup)
    (hcompat : wordCompatible R (ρ ++ [b, a, c] ++ σ)) :
    wordCompatible S (ρ ++ [a, c, b] ++ σ) := by
  have hρ : wordCompatible S ρ := by
    have hp := (List.pairwise_append.mp (List.pairwise_append.mp hcompat).1).1
    apply hp.imp_of_mem
    intro x y hx hy hR hS'
    rcases (hS y x).mp hS' with hnew | hold
    · have hn := (List.nodup_append.mp hw).1
      have hdis := (List.nodup_append.mp hn).2.2
      exact hdis y hy a (by simp) hnew.1
    · exact hR hold.1
  have hσ : wordCompatible S σ := by
    have hp := (List.pairwise_append.mp hcompat).2.1
    apply hp.imp_of_mem
    intro x y hx hy hR hS'
    rcases (hS y x).mp hS' with hnew | hold
    · have hdis := (List.nodup_append.mp hw).2.2
      exact hdis a (by simp) y hy hnew.1.symm
    · exact hR hold.1
  simp [wordCompatible, List.pairwise_append, List.pairwise_cons,
    List.nodup_append, List.nodup_cons] at hw hcompat
  simp only [wordCompatible, List.pairwise_append]
  refine ⟨⟨hρ, ?_, ?_⟩, hσ, ?_⟩
  all_goals simp [List.pairwise_cons, hS]; grind

end

end VerticalStripLLT.Components

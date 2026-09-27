import VerticalStripLLT.Components.BlockExtractor
import VerticalStripLLT.Components.ComponentWords

/-! Neutral reorderings of compatible and full words. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- If the two short forward edges are absent, `acb` and `bac` have the same
compatibility condition. -/
theorem wordCompatible_acb_bac_iff_of_no_short
    (R : V → V → Prop) (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (ρ σ : List V) {a b c : V} (habOrder : a < b) (hbcOrder : b < c)
    (hab : ¬ R a b) (hbc : ¬ R b c) :
    wordCompatible R (ρ ++ [a, c, b] ++ σ) ↔
      wordCompatible R (ρ ++ [b, a, c] ++ σ) := by
  have hba : ¬ R b a := by
    intro h
    exact (not_lt_of_ge (le_of_lt habOrder)) (hforward h)
  have hca : ¬ R c a := by
    intro h
    exact (not_lt_of_ge (le_of_lt (lt_trans habOrder hbcOrder))) (hforward h)
  have hcb : ¬ R c b := by
    intro h
    exact (not_lt_of_ge (le_of_lt hbcOrder)) (hforward h)
  simp [wordCompatible, List.pairwise_append, List.pairwise_cons, hab, hbc,
    hba, hca, hcb, and_assoc, and_left_comm, and_comm]

omit [LinearOrder V] in
/-- Full-word status is unchanged by the contextual `acb` to `bac` reorder. -/
theorem fullWord_acb_bac_iff
    (ρ σ : List V) {a b c : V} :
    fullWord (ρ ++ [a, c, b] ++ σ) ↔
      fullWord (ρ ++ [b, a, c] ++ σ) := by
  apply fullWord_perm_iff
  exact List.Perm.append_right σ (List.Perm.append_left ρ
    (List.perm_append_singleton b [a, c]))

omit [LinearOrder V] in
/-- Full-word status is unchanged by the contextual `acb` to `cab` reorder. -/
theorem fullWord_acb_cab_iff
    (ρ σ : List V) {a b c : V} :
    fullWord (ρ ++ [a, c, b] ++ σ) ↔
      fullWord (ρ ++ [c, a, b] ++ σ) := by
  apply fullWord_perm_iff
  exact List.Perm.append_right σ (List.Perm.append_left ρ
    (List.Perm.swap _ _ _))

omit [LinearOrder V] in
/-- Full-word status is unchanged by the contextual `acb` to `bca` reorder. -/
theorem fullWord_acb_bca_iff
    (ρ σ : List V) {a b c : V} :
    fullWord (ρ ++ [a, c, b] ++ σ) ↔
      fullWord (ρ ++ [b, c, a] ++ σ) := by
  apply fullWord_perm_iff
  have hp₁ : ([a, c, b] : List V).Perm [b, a, c] :=
    List.perm_append_singleton b [a, c]
  have hp₂ : ([b, a, c] : List V).Perm [b, c, a] :=
    List.Perm.cons b (List.Perm.swap _ _ _)
  exact List.Perm.append_right σ (List.Perm.append_left ρ (hp₁.trans hp₂))

end

end VerticalStripLLT.Components

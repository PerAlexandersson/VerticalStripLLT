import VerticalStripLLT.Components.GainCoefficientRecurrence
import VerticalStripLLT.Components.GainCoefficientBase
import VerticalStripLLT.Components.GainDeletionWitness
import VerticalStripLLT.Components.FiniteDeletionExpansion

/-! The finite gain companion for any semantics satisfying the actual deletion identity. -/

namespace VerticalStripLLT.Components.GainData

open Classical
open scoped BigOperators

noncomputable section

variable {V E M : Type*} [Fintype V] [DecidableEq E] [AddCommGroup M] (G : GainData V E)

/-- Edge-count induction with the independently defined companion coefficients.
The only semantic input is the signed deletion identity for `W`. -/
theorem expansion_of_deletionRecurrence (R : Finset E) (W : Finset E → M)
    (hacyclic : ∀ v, ¬Relation.TransGen (G.selectedRelation R) v v)
    (hW : ∀ X, X ⊆ R → ∀ w : G.DeletionWitness X,
      (∑ J ∈ w.optional.powerset,
        (-1 : ℤ) ^ J.card • W ((X \ w.optional) ∪ J)) = 0) :
    W R = ∑ F ∈ R.powerset, G.coefficient R F • W F := by
  apply eq_sum_coefficient_smul_of_deletion R W G.coefficient G.Balanced
    ?_ ?_ R Finset.Subset.rfl
  · intro X _ hX F _
    exact G.coefficient_eq_delta_of_balanced hX F
  · intro X hXR hX
    have hacyclicX : ∀ v, ¬Relation.TransGen (G.selectedRelation X) v v := by
      intro v hv
      apply hacyclic v
      apply Relation.TransGen.mono (r := G.selectedRelation X) _ v v hv
      rintro u w ⟨e, he, ht, hh⟩
      exact ⟨e, hXR he, ht, hh⟩
    obtain ⟨w⟩ := G.exists_deletionWitness hX hacyclicX
    refine ⟨w.optional, w.optional_subset, w.optional_nonempty, hW X hXR w, ?_⟩
    intro F _
    by_cases hFX : F ⊆ X
    · apply G.sum_powerset_coefficient_eq_zero (X \ w.optional) w.optional F
        ?_ ?_ w.positive w.negative w.negative_mem w.optional_mem w.positive_mem
        w.endpoint_perm w.excess
      · simpa only [Finset.sdiff_union_of_subset w.optional_subset] using hFX
      · exact Finset.disjoint_left.mpr (fun _ he hmem =>
          (Finset.mem_sdiff.mp he).2 hmem)
    · apply Finset.sum_eq_zero
      intro J hJ
      have hchild : (X \ w.optional) ∪ J ⊆ X :=
        Finset.union_subset Finset.sdiff_subset
          ((Finset.mem_powerset.mp hJ).trans w.optional_subset)
      have hbad : ¬F ⊆ (X \ w.optional) ∪ J := fun h => hFX (h.trans hchild)
      rw [G.coefficient_eq_zero_of_not_subset hbad, mul_zero]

end

end VerticalStripLLT.Components.GainData

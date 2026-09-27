import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff

/-! Reindex subset sums with a required portion of the selected set. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {E M : Type*} [DecidableEq E] [AddCommMonoid M]

/-- Subsets containing the part of `F` outside `B` are parametrized by their
    portion outside `F`. -/
theorem sum_powerset_required_subset_eq_sdiff_union
    (B N F : Finset E) (hFN : F ⊆ B ∪ N) (hBN : Disjoint B N)
    (f : Finset E → M) :
    (∑ J ∈ N.powerset,
      if F ⊆ B ∪ J then f J else 0) =
      ∑ J' ∈ (N \ F).powerset, f ((F ∩ N) ∪ J') := by
  classical
  have recover (J : Finset E) (hJ : J ⊆ N) (hF : F ⊆ B ∪ J) :
      (F ∩ N) ∪ (J \ F) = J := by
    ext x
    have hdisj := Finset.disjoint_left.mp hBN
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    have hFx := @hFN x
    have hFJ := @hF x
    simp only [Finset.mem_union] at hFx hFJ
    grind
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun J _ => J \ F) ?_ ?_ ?_ ?_
  · intro J hJ
    obtain ⟨hJN, _⟩ := Finset.mem_filter.mp hJ
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hxJ, hxF⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_powerset.mp hJN hxJ, hxF⟩
  · intro J hJ K hK heq
    obtain ⟨hJN, hFJ⟩ := Finset.mem_filter.mp hJ
    obtain ⟨hKN, hFK⟩ := Finset.mem_filter.mp hK
    rw [← recover J (Finset.mem_powerset.mp hJN) hFJ,
      ← recover K (Finset.mem_powerset.mp hKN) hFK, heq]
  · intro J hJ
    have hsub := Finset.mem_powerset.mp hJ
    refine ⟨(F ∩ N) ∪ J, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, ?_⟩
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_inter] at hx
      rcases hx with h | h
      · exact h.2
      · exact (Finset.mem_sdiff.mp (hsub h)).1
    · intro x hx
      have h := hFN hx
      simp only [Finset.mem_union, Finset.mem_inter] at h ⊢
      tauto
    · ext x
      have h := @hsub x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h ⊢
      tauto
  · intro J hJ
    obtain ⟨hJN, hFJ⟩ := Finset.mem_filter.mp hJ
    rw [recover J (Finset.mem_powerset.mp hJN) hFJ]

end

end VerticalStripLLT.Components

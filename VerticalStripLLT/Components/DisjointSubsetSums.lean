import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset

/-! Reindexing disjoint pairs of subsets by their union and second subset. -/

namespace VerticalStripLLT.Components

open scoped BigOperators
open Classical

noncomputable section

variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

theorem sum_powerset_disjoint_eq_union
    (S : Finset α) (f : Finset α → Finset α → M) :
    (∑ P ∈ S.powerset, ∑ T ∈ S.powerset,
      if Disjoint P T then f P T else 0) =
      ∑ B ∈ S.powerset, ∑ T ∈ B.powerset, f (B \ T) T := by
  let domain : Finset (Finset α × Finset α) :=
    (S.powerset.product S.powerset).filter (fun p => Disjoint p.1 p.2)
  let codomain : Finset (Σ _ : Finset α, Finset α) :=
    S.powerset.sigma (fun B => B.powerset)
  have hleft :
      (∑ P ∈ S.powerset, ∑ T ∈ S.powerset,
        if Disjoint P T then f P T else 0) =
        ∑ p ∈ domain, f p.1 p.2 := by
    rw [← Finset.sum_product']
    change (∑ p ∈ S.powerset.product S.powerset,
      if Disjoint p.1 p.2 then f p.1 p.2 else 0) = _
    rw [← Finset.sum_filter]
  have hright :
      (∑ B ∈ S.powerset, ∑ T ∈ B.powerset, f (B \ T) T) =
        ∑ q ∈ codomain, f (q.1 \ q.2) q.2 := by
    rw [Finset.sum_sigma']
  rw [hleft, hright]
  refine Finset.sum_bij
    (fun p _ => (⟨p.1 ∪ p.2, p.2⟩ : Σ _ : Finset α, Finset α)) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpS := (Finset.mem_product.mp hp'.1).1
    have hpT := (Finset.mem_product.mp hp'.1).2
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr
        (Finset.union_subset (Finset.mem_powerset.mp hpS)
          (Finset.mem_powerset.mp hpT))
    · exact Finset.mem_powerset.mpr Finset.subset_union_right
  · intro p hp q hq heq
    have hfirst := congrArg
      (fun z : Σ _ : Finset α, Finset α => z.1) heq
    have hsecond := congrArg
      (fun z : Σ _ : Finset α, Finset α => z.2) heq
    dsimp only at hfirst hsecond
    apply Prod.ext
    · calc
        p.1 = (p.1 ∪ p.2) \ p.2 :=
          (Finset.union_sdiff_cancel_right (Finset.mem_filter.mp hp).2).symm
        _ = (q.1 ∪ q.2) \ q.2 := by rw [hfirst, hsecond]
        _ = q.1 := Finset.union_sdiff_cancel_right (Finset.mem_filter.mp hq).2
    · exact hsecond
  · intro q hq
    rcases q with ⟨B, T⟩
    have hq' := Finset.mem_sigma.mp hq
    let p : Finset α × Finset α := (B \ T, T)
    have hp : p ∈ domain := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, Finset.sdiff_disjoint⟩
      · exact Finset.mem_powerset.mpr
          (Finset.sdiff_subset.trans (Finset.mem_powerset.mp hq'.1))
      · exact Finset.mem_powerset.mpr
          ((Finset.mem_powerset.mp hq'.2).trans (Finset.mem_powerset.mp hq'.1))
    refine ⟨p, hp, ?_⟩
    dsimp [p]
    rw [Finset.sdiff_union_of_subset (Finset.mem_powerset.mp hq'.2)]
  · intro p hp
    change f p.1 p.2 = f ((p.1 ∪ p.2) \ p.2) p.2
    rw [Finset.union_sdiff_cancel_right (Finset.mem_filter.mp hp).2]

end

end VerticalStripLLT.Components

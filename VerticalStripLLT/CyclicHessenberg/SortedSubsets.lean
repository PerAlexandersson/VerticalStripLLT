import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists

set_option autoImplicit false

/-! Reindex sublists of a sorted support by the corresponding finset subsets. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators List

variable {V R : Type*} [LinearOrder V] [AddCommMonoid R]

private theorem list_sum_map_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → R) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp hl with ⟨ha, hl⟩
    simp [ha, ih hl]

/-- A sublist of a sorted finset list is the sort of its own finset. -/
private theorem sort_toFinset_eq_self_of_sublist (S : Finset V) {l : List V}
    (hl : l <+ S.sort) : l.toFinset.sort = l := by
  apply (List.toFinset_sort (r := (· ≤ ·)) (hl.nodup (Finset.sort_nodup _ _))).2
  exact (Finset.pairwise_sort (· ≤ ·) S).sublist hl

/-- Sum a weight over all sublists of the increasing list of `S` by subsets of `S`. -/
theorem sum_sublists_sort (S : Finset V) (f : List V → R) :
    (S.sort.sublists.map f).sum = ∑ T ∈ S.powerset, f T.sort := by
  classical
  have hsortNodup : S.sort.Nodup := Finset.sort_nodup _ _
  have hsublistsNodup : S.sort.sublists.Nodup := List.nodup_sublists.mpr hsortNodup
  rw [list_sum_map_eq_finset_sum _ hsublistsNodup]
  apply Finset.sum_bij (fun l _ => l.toFinset)
  · intro l hl
    rw [Finset.mem_powerset]
    intro x hx
    have hsub : l <+ S.sort := List.mem_sublists.mp (List.mem_toFinset.mp hl)
    have hxSort : x ∈ S.sort := hsub.subset (by simpa using hx)
    simpa using hxSort
  · intro l hl l' hl' hEq
    have hsub : l <+ S.sort := List.mem_sublists.mp (List.mem_toFinset.mp hl)
    have hsub' : l' <+ S.sort := List.mem_sublists.mp (List.mem_toFinset.mp hl')
    have hperm := List.perm_of_nodup_nodup_toFinset_eq
      (hsub.nodup hsortNodup) (hsub'.nodup hsortNodup) hEq
    exact List.Perm.eq_of_pairwise'
      ((Finset.pairwise_sort (· ≤ ·) S).sublist hsub)
      ((Finset.pairwise_sort (· ≤ ·) S).sublist hsub') hperm
  · intro T hT
    have hTsub : T ⊆ S := Finset.mem_powerset.mp hT
    have hperm : T.sort <+~ S.sort :=
      List.Nodup.subperm (Finset.sort_nodup _ _) (by
        intro x hx
        have hxT : x ∈ T := by simpa using hx
        have hxS := hTsub hxT
        simpa using hxS)
    have hsub : T.sort <+ S.sort :=
      List.sublist_of_subperm_of_sortedLE hperm
        ((Finset.pairwise_sort (· ≤ ·) T).sortedLE)
        ((Finset.pairwise_sort (· ≤ ·) S).sortedLE)
    refine ⟨T.sort, List.mem_toFinset.mpr (List.mem_sublists.mpr hsub), ?_⟩
    simp
  · intro l hl
    have hsub : l <+ S.sort := List.mem_sublists.mp (List.mem_toFinset.mp hl)
    exact congrArg f (sort_toFinset_eq_self_of_sublist S hsub).symm

end VerticalStripLLT.CyclicHessenberg

import VerticalStripLLT.Components.WordProof.BlockExtractor
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Reindex ordered subwords by the finite sets of selected entries. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

private theorem filter_mem_toFinset_eq_of_sublist {α : Type*} [DecidableEq α]
    (L S : List α) (hL : L.Nodup) (hS : S.Sublist L) :
    L.filter (fun v => decide (v ∈ S.toFinset)) = S := by
  have hperm : (L.filter (fun v => decide (v ∈ S.toFinset))).Perm S := by
    apply List.perm_of_nodup_nodup_toFinset_eq (hL.filter _)
      (hL.sublist hS)
    ext v
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro hv
      exact hv.2
    · intro hv
      exact ⟨hS.subset hv, hv⟩
  exact (List.Nodup.perm_iff_eq_of_sublist hL (List.filter_sublist)
    hS).mp hperm

private theorem filter_mem_toFinset_eq_of_subset {α : Type*} [DecidableEq α]
    (L : List α) (B : Finset α) (hB : B ⊆ L.toFinset) :
    (L.filter (fun v => decide (v ∈ B))).toFinset = B := by
  ext v
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hv
    exact hv.2
  · intro hv
    exact ⟨List.mem_toFinset.mp (hB hv), hv⟩

/-- Ordered subwords of a nodup list are indexed by subsets of its entries. -/
theorem sum_sublists'_eq_sum_powerset_filter {α A : Type*}
    [DecidableEq α] [AddCommMonoid A] (L : List α) (hL : L.Nodup)
    (f : List α → A) :
    (L.sublists'.map f).sum =
      ∑ B ∈ L.toFinset.powerset,
        f (L.filter (fun v => decide (v ∈ B))) := by
  classical
  rw [← List.sum_toFinset f (List.nodup_sublists'.mpr hL)]
  apply Finset.sum_bij (fun S _ => S.toFinset)
  · intro S hS
    have hsub : S.Sublist L :=
      List.mem_sublists'.mp (List.mem_toFinset.mp hS)
    exact Finset.mem_powerset.mpr (fun v hv =>
      List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hv)))
  · intro S hS T hT hEq
    have hSsub : S.Sublist L :=
      List.mem_sublists'.mp (List.mem_toFinset.mp hS)
    have hTsub : T.Sublist L :=
      List.mem_sublists'.mp (List.mem_toFinset.mp hT)
    apply (List.Nodup.perm_iff_eq_of_sublist hL hSsub hTsub).mp
    exact List.perm_of_nodup_nodup_toFinset_eq
      (hL.sublist hSsub) (hL.sublist hTsub) hEq
  · intro B hB
    have hsub : B ⊆ L.toFinset := Finset.mem_powerset.mp hB
    let S := L.filter (fun v => decide (v ∈ B))
    have hSsub : S.Sublist L := by
      exact List.filter_sublist
    have hSfin : S.toFinset = B := by
      exact filter_mem_toFinset_eq_of_subset L B hsub
    refine ⟨S, List.mem_toFinset.mpr (List.mem_sublists'.mpr hSsub), hSfin⟩
  · intro S hS
    rw [filter_mem_toFinset_eq_of_sublist L S hL
      (List.mem_sublists'.mp (List.mem_toFinset.mp hS))]

theorem length_filter_mem_toFinset_eq_card {α : Type*} [DecidableEq α]
    (L : List α) (hL : L.Nodup) (B : Finset α) (hB : B ⊆ L.toFinset) :
    (L.filter (fun v => decide (v ∈ B))).length = B.card := by
  classical
  have hfilter := filter_mem_toFinset_eq_of_subset L B hB
  rw [← List.toFinset_card_of_nodup (hL.filter _), hfilter]

/-- Filtering an increasing sorted word gives the increasing word of the subset. -/
theorem incWord_filter_mem_eq_incWord {V : Type*} [LinearOrder V]
    (S B : Finset V) (hB : B ⊆ S) :
    (incWord S).filter (fun v => decide (v ∈ B)) = incWord B := by
  classical
  apply List.SortedLT.eq_of_mem_iff
    ((Finset.sortedLT_sort S).pairwise.filter _).sortedLT
    (Finset.sortedLT_sort B)
  intro v
  simp only [List.mem_filter, decide_eq_true_eq, Finset.mem_sort]
  constructor
  · exact fun hv => hv.2
  · intro hv
    exact ⟨hB hv, hv⟩

/-- Filtering a decreasing sorted word gives the decreasing word of the subset. -/
theorem decWord_filter_mem_eq_decWord {V : Type*} [LinearOrder V]
    (S B : Finset V) (hB : B ⊆ S) :
    (decWord S).filter (fun v => decide (v ∈ B)) = decWord B := by
  classical
  apply List.SortedGT.eq_of_mem_iff
    ((Finset.sortedGT_sort S).pairwise.filter _).sortedGT
    (Finset.sortedGT_sort B)
  intro v
  simp only [List.mem_filter, decide_eq_true_eq, Finset.mem_sort]
  constructor
  · exact fun hv => hv.2
  · intro hv
    exact ⟨hB hv, hv⟩

end

end VerticalStripLLT.Components

import VerticalStripLLT.Components.GainBalancedWitness
import Mathlib.Data.List.Perm.Basic

/-! List-level projections and endpoint transport for signed edges. -/

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- The original edges carrying the forward (`true`) signed copy. -/
def forwardEdges (L : List (E × Bool)) : List E :=
  (L.filter (fun e => e.2)).map Prod.fst

/-- The original edges carrying the backward (`false`) signed copy. -/
def backwardEdges (L : List (E × Bool)) : List E :=
  (L.filter (fun e => !e.2)).map Prod.fst

theorem mem_forwardEdges_of_mem {L : List (E × Bool)} {e : E}
    (h : (e, true) ∈ L) : e ∈ forwardEdges L := by
  simp [forwardEdges, h]

theorem mem_backwardEdges_of_mem {L : List (E × Bool)} {e : E}
    (h : (e, false) ∈ L) : e ∈ backwardEdges L := by
  simp [backwardEdges, h]

theorem mem_forwardEdges_iff {L : List (E × Bool)} {e : E} :
    e ∈ forwardEdges L ↔ (e, true) ∈ L := by
  simp [forwardEdges]

theorem mem_backwardEdges_iff {L : List (E × Bool)} {e : E} :
    e ∈ backwardEdges L ↔ (e, false) ∈ L := by
  simp [backwardEdges]

theorem sum_map_doubled_gain_eq_forward_sub_backward (L : List (E × Bool)) :
    (L.map G.doubled.gain).sum =
      ((forwardEdges L).map G.gain).sum -
        ((backwardEdges L).map G.gain).sum := by
  induction L with
  | nil => simp [forwardEdges, backwardEdges]
  | cons p L ih =>
    cases p with
    | mk e b =>
      cases b <;> simp [forwardEdges, backwardEdges, GainData.doubled, ih] <;> ring

private theorem filter_bool_partition_perm {α : Type*} (L : List α)
    (p : α → Bool) :
    (L.filter p ++ L.filter (fun a => !p a)).Perm L := by
  exact List.filter_append_perm p L

private theorem map_doubled_head_filter_true (L : List (E × Bool)) :
    (L.filter (fun e => e.2)).map G.doubled.head =
      (forwardEdges L).map G.head := by
  induction L with
  | nil => simp [forwardEdges]
  | cons p L ih =>
    cases p with
    | mk e b =>
      cases b <;> simp [forwardEdges, GainData.doubled, ih]

private theorem map_doubled_head_filter_false (L : List (E × Bool)) :
    (L.filter (fun e => !e.2)).map G.doubled.head =
      (backwardEdges L).map G.tail := by
  induction L with
  | nil => simp [backwardEdges]
  | cons p L ih =>
    cases p with
    | mk e b =>
      cases b <;> simp [backwardEdges, GainData.doubled, ih]

private theorem map_doubled_tail_filter_true (L : List (E × Bool)) :
    (L.filter (fun e => e.2)).map G.doubled.tail =
      (forwardEdges L).map G.tail := by
  induction L with
  | nil => simp [forwardEdges]
  | cons p L ih =>
    cases p with
    | mk e b =>
      cases b <;> simp [forwardEdges, GainData.doubled, ih]

private theorem map_doubled_tail_filter_false (L : List (E × Bool)) :
    (L.filter (fun e => !e.2)).map G.doubled.tail =
      (backwardEdges L).map G.head := by
  induction L with
  | nil => simp [backwardEdges]
  | cons p L ih =>
    cases p with
    | mk e b =>
      cases b <;> simp [backwardEdges, GainData.doubled, ih]

/-- A balanced endpoint multiset transports to the two signed projections. -/
theorem signedEndpointPerm_of_doubledEndpointPerm
    {L : List (E × Bool)}
    (hperm : (L.map G.doubled.head).Perm (L.map G.doubled.tail)) :
    ((forwardEdges L).map G.head ++ (backwardEdges L).map G.tail).Perm
      ((forwardEdges L).map G.tail ++ (backwardEdges L).map G.head) := by
  have hpartition := filter_bool_partition_perm L (fun e : E × Bool => e.2)
  have hhead := hpartition.map (fun e => G.doubled.head e)
  have htail := hpartition.map (fun e => G.doubled.tail e)
  rw [List.map_append, map_doubled_head_filter_true,
    map_doubled_head_filter_false] at hhead
  rw [List.map_append, map_doubled_tail_filter_true,
    map_doubled_tail_filter_false] at htail
  exact hhead.trans (hperm.trans htail.symm)

end

end VerticalStripLLT.Components.GainData

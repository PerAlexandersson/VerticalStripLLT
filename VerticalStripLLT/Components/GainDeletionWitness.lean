import VerticalStripLLT.Components.GainWalkEdges
import VerticalStripLLT.Components.SignedEdgeLists
import VerticalStripLLT.Components.SignedListCancellation
import VerticalStripLLT.Components.OrderedPartitionDAG

/-! Every unbalanced acyclic selection has a finite signed deletion witness. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open Classical

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq E] (G : GainData V E)

/-- Cancel opposite edge occurrences in a positive doubled closed walk. -/
theorem exists_disjoint_signedLists {F : Finset E} (hF : ¬G.Balanced F) :
    ∃ P N : List E, (∀ e ∈ P, e ∈ F) ∧ (∀ e ∈ N, e ∈ F) ∧ P.Disjoint N ∧
      (P.map G.head ++ N.map G.tail).Perm (P.map G.tail ++ N.map G.head) ∧
      (N.map G.gain).sum < (P.map G.gain).sum := by
  obtain ⟨v, q, hpos⟩ := G.exists_positive_doubled_closedWalk hF
  let L := G.doubled.walkEdges q
  let P := forwardEdges L
  let N := backwardEdges L
  have hP : ∀ e ∈ P, e ∈ F := by
    intro e he
    exact mem_doubledSelection.mp
      (G.doubled.mem_walkEdges q (mem_forwardEdges_iff.mp he))
  have hN : ∀ e ∈ N, e ∈ F := by
    intro e he
    exact mem_doubledSelection.mp
      (G.doubled.mem_walkEdges q (mem_backwardEdges_iff.mp he))
  have hperm := G.signedEndpointPerm_of_doubledEndpointPerm
    (G.doubled.closedWalkEdges_endpoint_perm q)
  have hexcess : (N.map G.gain).sum < (P.map G.gain).sum := by
    rw [G.doubled.walkGain_eq_sum_walkEdges,
      G.sum_map_doubled_gain_eq_forward_sub_backward] at hpos
    change 0 < (P.map G.gain).sum - (N.map G.gain).sum at hpos
    lia
  refine ⟨residualPositive P N, residualNegative P N,
    (fun e he => hP e (mem_residualPositive he)),
    (fun e he => hN e (mem_residualNegative he)), residual_disjoint P N,
    residual_endpoint_perm G.tail G.head hperm, ?_⟩
  have hd := residual_gain_sub_eq G.gain P N
  lia

/-- A nonempty endpoint-balanced forward list would contradict the existence of a DAG source. -/
theorem eq_nil_of_endpoint_perm {F : Finset E}
    (hacyclic : ∀ v, ¬Relation.TransGen (G.selectedRelation F) v v)
    (P : List E) (hP : ∀ e ∈ P, e ∈ F)
    (hperm : (P.map G.head).Perm (P.map G.tail)) : P = [] := by
  by_contra hnonempty
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil P hnonempty
  let S := (P.map G.tail).toFinset
  have hS : S.Nonempty :=
    ⟨G.tail e, List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)⟩
  apply OrderedPartitions.edgeHeads_ne_of_acyclic (G.selectedRelation F) hacyclic S hS
  ext v
  simp only [OrderedPartitions.edgeHeads, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hv
    have hvhead := hperm.mem_iff.mpr (List.mem_toFinset.mp hv)
    obtain ⟨f, hf, hhead⟩ := List.mem_map.mp hvhead
    exact ⟨hv, G.tail f, List.mem_toFinset.mpr (List.mem_map.mpr ⟨f, hf, rfl⟩),
      ⟨f, hP f hf, rfl, hhead⟩⟩

/-- Concrete data for a signed deletion reducing the selected edge set. -/
structure DeletionWitness (F : Finset E) where
  optional : Finset E
  positive : List E
  negative : List E
  optional_subset : optional ⊆ F
  optional_nonempty : optional.Nonempty
  positive_ne_nil : positive ≠ []
  positive_mem : ∀ e ∈ positive, e ∈ F \ optional
  negative_mem : ∀ e ∈ negative, e ∈ optional
  optional_mem : ∀ e ∈ optional, e ∈ negative
  endpoint_perm : (positive.map G.head ++ negative.map G.tail).Perm
    (positive.map G.tail ++ negative.map G.head)
  excess : (negative.map G.gain).sum < (positive.map G.gain).sum

/-- Unbalancedness in a finite DAG supplies every hypothesis of both deletion recurrences. -/
theorem exists_deletionWitness {F : Finset E} (hF : ¬G.Balanced F)
    (hacyclic : ∀ v, ¬Relation.TransGen (G.selectedRelation F) v v) :
    Nonempty (G.DeletionWitness F) := by
  obtain ⟨P, N, hP, hN, hdisj, hperm, hexcess⟩ := G.exists_disjoint_signedLists hF
  have hPn : P ≠ [] := by
    intro hp
    have hn : N = [] := by
      apply G.eq_nil_of_endpoint_perm hacyclic N hN
      simpa only [hp, List.map_nil, List.nil_append] using hperm.symm
    simp [hp, hn] at hexcess
  have hNn : N ≠ [] := by
    intro hn
    apply hPn
    apply G.eq_nil_of_endpoint_perm hacyclic P hP
    simpa only [hn, List.map_nil, List.append_nil] using hperm
  refine ⟨{
    optional := N.toFinset
    positive := P
    negative := N
    optional_subset := fun e he => hN e (List.mem_toFinset.mp he)
    optional_nonempty := ?_
    positive_ne_nil := hPn
    positive_mem := ?_
    negative_mem := fun _ he => List.mem_toFinset.mpr he
    optional_mem := fun _ he => List.mem_toFinset.mp he
    endpoint_perm := hperm
    excess := hexcess }⟩
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil N hNn
    exact ⟨e, List.mem_toFinset.mpr he⟩
  · intro e he
    exact Finset.mem_sdiff.mpr ⟨hP e he, fun h => hdisj he (List.mem_toFinset.mp h)⟩

end

end VerticalStripLLT.Components.GainData

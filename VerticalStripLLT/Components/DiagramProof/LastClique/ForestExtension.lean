import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Extend a required spanning forest to a connected edge set of any feasible size. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [Fintype V]

/-- Required forest edges can be retained at every connected spanning size.
The lower bound is additive, including the one-vertex case without subtraction. -/
theorem exists_connected_extension_card (G F : SimpleGraph V) (hG : G.Connected)
    (hFG : F ≤ G) (hF : F.IsAcyclic) (t : ℕ)
    (hlower : Fintype.card V ≤ t + 1) (hupper : t ≤ Nat.card G.edgeSet) :
    ∃ H : SimpleGraph V, F ≤ H ∧ H ≤ G ∧ H.Connected ∧ Nat.card H.edgeSet = t := by
  classical
  obtain ⟨T, hFT, hTG, hT⟩ := hG.exists_isTree_le_of_le_of_isAcyclic hFG hF
  have hTcard := hT.card_edgeFinset
  have hTle : T.edgeFinset.card ≤ t := by lia
  have htG : t ≤ G.edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using hupper
  obtain ⟨E, hTE, hEG, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq (SimpleGraph.edgeFinset_mono hTG) hTle htG
  let H := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hTH : T ≤ H := by
    apply (SimpleGraph.le_fromEdgeSet_iff _ _).mpr
    intro e he
    exact hTE (SimpleGraph.mem_edgeFinset.mpr he)
  have hHG : H ≤ G := by
    rw [← SimpleGraph.fromEdgeSet_edgeSet G]
    apply SimpleGraph.fromEdgeSet_mono
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp (hEG he)
  have hHE : H.edgeFinset = E := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset]
    ext e
    simp only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe]
    exact ⟨fun h => h.1, fun he =>
      ⟨he, G.not_isDiag_of_mem_edgeFinset (hEG he)⟩⟩
  refine ⟨H, hFT.trans hTH, hHG, hT.connected.mono hTH, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hHE, hEcard]

/-- If a nonrequired edge is removable, every feasible size below the full size
has a connected extension that omits it. -/
theorem exists_connected_extension_card_avoiding (G F : SimpleGraph V)
    (d : Sym2 V) (hconnected : (G.deleteEdges {d}).Connected)
    (hFG : F ≤ G) (hF : F.IsAcyclic) (hdG : d ∈ G.edgeSet) (hdF : d ∉ F.edgeSet)
    (t : ℕ) (hlower : Fintype.card V ≤ t + 1) (hupper : t + 1 ≤ Nat.card G.edgeSet) :
    ∃ H : SimpleGraph V, F ≤ H ∧ H ≤ G ∧ H.Connected ∧
      Nat.card H.edgeSet = t ∧ d ∉ H.edgeSet := by
  classical
  have hFd : F ≤ G.deleteEdges {d} := by
    apply SimpleGraph.edgeSet_subset_edgeSet.mp
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨SimpleGraph.edgeSet_mono hFG he, fun h => hdF (Set.mem_singleton_iff.mp h ▸ he)⟩
  have hdeleted : (G.deleteEdges {d}).edgeFinset = G.edgeFinset.erase d := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase]
    exact and_comm
  have ht : t ≤ Nat.card (G.deleteEdges {d}).edgeSet := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hdeleted,
      Finset.card_erase_of_mem (SimpleGraph.mem_edgeFinset.mpr hdG)]
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hupper
    lia
  obtain ⟨H, hFH, hHG, hH, hcard⟩ :=
    exists_connected_extension_card (G.deleteEdges {d}) F hconnected hFd hF t hlower ht
  refine ⟨H, hFH, hHG.trans (G.deleteEdges_le {d}), hH, hcard, ?_⟩
  intro hdH
  have hd := SimpleGraph.edgeSet_mono hHG hdH
  simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
    not_true_eq_false, and_false] at hd

end VerticalStripLLT.Circular.DiagramProof

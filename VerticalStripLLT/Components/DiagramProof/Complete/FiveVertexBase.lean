import VerticalStripLLT.Components.DiagramProof.Complete.FiveVertexPaths
import VerticalStripLLT.Components.DiagramProof.Relations.ThreePositionPaths
import VerticalStripLLT.Components.DiagramProof.Complete.Chain

/-! The complete-diagram active-layer theorem on five vertices. -/

namespace VerticalStripLLT.Circular.DiagramProof

set_option backward.isDefEq.respectTransparency false

namespace FiveVertex

/-- The chord position `13` of the complete diagram on five vertices. -/
noncomputable def chord13 : Edge (completeDiagram 4).area := completeEdge 4 1 3 (by decide)
/-- The chord position `14` of the complete diagram on five vertices. -/
noncomputable def chord14 : Edge (completeDiagram 4).area := completeEdge 4 1 4 (by decide)
/-- The chord position `24` of the complete diagram on five vertices. -/
noncomputable def chord24 : Edge (completeDiagram 4).area := completeEdge 4 2 4 (by decide)

theorem chord_positions : completeChordPositions 4 = {chord13, chord14, chord24} := by
  classical
  ext e
  rw [mem_completeChordPositions]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hbound := e.head.isLt
    have htail : e.tail.val = 1 ∨ e.tail.val = 2 := by lia
    have identify (f : Edge (completeDiagram 4).area)
        (ht : e.tail.val = f.tail.val) (hh : e.head.val = f.head.val) : e = f :=
      (completeDiagram 4).endpointEmbedding.injective (Prod.ext (Fin.ext ht) (Fin.ext hh))
    rcases htail with ht | ht
    · have hhead : e.head.val = 3 ∨ e.head.val = 4 := by lia
      rcases hhead with hh | hh
      · exact Or.inl (identify chord13 (by simpa [chord13] using ht) hh)
      · exact Or.inr (Or.inl (identify chord14 (by simpa [chord14] using ht) hh))
    · have hh : e.head.val = 4 := by lia
      exact Or.inr (Or.inr (identify chord24 (by simpa [chord24] using ht) hh))
  · rintro (rfl | rfl | rfl) <;> simp [chord13, chord14, chord24]

/-- The common chain together with a set of chords, as endpoint pairs. -/
noncomputable def pairsFor (S : Finset (Edge (completeDiagram 4).area)) : Pairs :=
  chain ∪ S.image (fun e => (e.tail, e.head))

theorem pairsFor_forward (S : Finset (Edge (completeDiagram 4).area)) :
    ForwardPairs (pairsFor S) := by
  intro u v h
  rcases Finset.mem_union.mp h with hc | hs
  · exact (show ForwardPairs chain by decide) u v hc
  · obtain ⟨e, _, he⟩ := Finset.mem_image.mp hs
    obtain ⟨ht, hh⟩ := Prod.mk.inj he
    rw [← ht, ← hh]
    exact complete_forward 4 e

/-- Compare endpoint selections with the actual chain-state representation. -/
theorem state_pairsFor (S : Finset (Edge (completeDiagram 4).area)) :
    state (pairsFor S) (pairsFor_forward S) = completeChainState 4 S := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    state_selected, completeChainState_selected_iff (by decide)]
  have hc : ∀ u v : Fin 5, (u, v) ∈ chain ↔
      (u = 0 ∧ v = Fin.last 4) ∨ (0 < u.val ∧ u.val + 1 = v.val) := by decide
  simp only [pairsFor, Finset.mem_union, Finset.mem_image, Prod.mk.injEq, hc]
  tauto

private theorem pairsFor_singletons :
    pairsFor {chord13} = pairs13 ∧ pairsFor {chord14} = pairs14 ∧
      pairsFor {chord24} = pairs24 := by
  classical
  simp [pairsFor, chord13, chord14, chord24, pairs13, pairs14, pairs24,
    Finset.union_singleton]

private theorem pairsFor_pairs :
    pairsFor {chord13, chord24} = pairs13_24 ∧
      pairsFor {chord14, chord24} = pairs14_24 ∧
      pairsFor {chord13, chord14} = pairs13_14 := by
  classical
  simp [pairsFor, chord13, chord14, chord24, pairs13_24, pairs14_24, pairs13_14,
    Finset.union_insert, Finset.union_singleton]

theorem chain_path13_14 : Relation.ReflTransGen (Flip (completeDiagram 4))
    (completeChainState 4 {chord13}) (completeChainState 4 {chord14}) := by
  rw [← state_pairsFor, ← state_pairsFor]
  simpa only [pairsFor_singletons.1, pairsFor_singletons.2.1] using path13_14

theorem chain_path14_24 : Relation.ReflTransGen (Flip (completeDiagram 4))
    (completeChainState 4 {chord14}) (completeChainState 4 {chord24}) := by
  rw [← state_pairsFor, ← state_pairsFor]
  simpa only [pairsFor_singletons.2.1, pairsFor_singletons.2.2] using path14_24

theorem chain_path13_24_to14_24 : Relation.ReflTransGen (Flip (completeDiagram 4))
    (completeChainState 4 {chord13, chord24})
    (completeChainState 4 {chord14, chord24}) := by
  rw [← state_pairsFor, ← state_pairsFor]
  simpa only [pairsFor_pairs.1, pairsFor_pairs.2.1] using path13_24_to14_24

theorem chain_path14_24_to13_14 : Relation.ReflTransGen (Flip (completeDiagram 4))
    (completeChainState 4 {chord14, chord24})
    (completeChainState 4 {chord13, chord14}) := by
  rw [← state_pairsFor, ← state_pairsFor]
  simpa only [pairsFor_pairs.2.1, pairsFor_pairs.2.2] using path14_24_to13_14

end FiveVertex

/-- The four explicit paths connect every equal-size subset of the three chord positions. -/
theorem completeChainState_reachable_five
    (S T : Finset (Edge (completeDiagram 4).area))
    (hS : S ⊆ completeChordPositions 4) (hT : T ⊆ completeChordPositions 4)
    (hcard : S.card = T.card) :
    Relation.ReflTransGen (Flip (completeDiagram 4))
      (completeChainState 4 S) (completeChainState 4 T) := by
  classical
  have hab : FiveVertex.chord13 ≠ FiveVertex.chord14 := by
    intro h
    have hh := congrArg (fun e : Edge (completeDiagram 4).area => e.head.val) h
    norm_num [FiveVertex.chord13, FiveVertex.chord14] at hh
  have hac : FiveVertex.chord13 ≠ FiveVertex.chord24 := by
    intro h
    have ht := congrArg (fun e : Edge (completeDiagram 4).area => e.tail.val) h
    norm_num [FiveVertex.chord13, FiveVertex.chord24] at ht
  have hbc : FiveVertex.chord14 ≠ FiveVertex.chord24 := by
    intro h
    have ht := congrArg (fun e : Edge (completeDiagram 4).area => e.tail.val) h
    norm_num [FiveVertex.chord14, FiveVertex.chord24] at ht
  rw [FiveVertex.chord_positions] at hS hT
  exact fixed_card_connectivity_on_three_positions hab hac hbc
    (completeChainState 4) (Flip (completeDiagram 4)) (fun _ _ h => flip_symm _ h)
    FiveVertex.chain_path13_14 FiveVertex.chain_path14_24
    FiveVertex.chain_path13_24_to14_24 FiveVertex.chain_path14_24_to13_14 hS hT hcard

/-- Every two connected five-vertex states covering `04` and having equal counts connect. -/
theorem complete_reachable_five (θ η : Orientation (completeDiagram 4))
    (hθ : SelectedConnected θ) (hcθ : Cover θ 0 (Fin.last 4))
    (hη : SelectedConnected η) (hcη : Cover η 0 (Fin.last 4))
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip (completeDiagram 4)) θ η := by
  obtain ⟨α, hθα, hrowα, hchainα⟩ := exists_complete_chain 3 θ hcθ hθ
  obtain ⟨β, hηβ, hrowβ, hchainβ⟩ := exists_complete_chain 3 η hcη hη
  have hcount : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hηβ))
  have hcard : (selectedCompleteChords α).card = (selectedCompleteChords β).card := by
    have hα := totalSelected_eq_chain_add_chords α hrowα hchainα
    have hβ := totalSelected_eq_chain_add_chords β hrowβ hchainβ
    lia
  have hαβ := completeChainState_reachable_five
    (selectedCompleteChords α) (selectedCompleteChords β)
    (selectedCompleteChords_subset α) (selectedCompleteChords_subset β) hcard
  rw [← eq_completeChainState_of_chain α hrowα hchainα,
    ← eq_completeChainState_of_chain β hrowβ hchainβ] at hαβ
  have reverse {σ τ : Orientation (completeDiagram 4)}
      (h : Relation.ReflTransGen (Flip (completeDiagram 4)) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram 4)) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  exact hθα.trans (hαβ.trans (reverse hηβ))

end VerticalStripLLT.Circular.DiagramProof

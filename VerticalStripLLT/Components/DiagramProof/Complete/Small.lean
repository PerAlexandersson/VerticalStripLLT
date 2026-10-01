import VerticalStripLLT.Components.DiagramProof.Complete.Chain
import VerticalStripLLT.Components.DiagramProof.Complete.Chords

/-! Complete diagrams with at most four vertices have at most one chord position. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- Two chord sets of the same size are equal when the greatest label is at most three. -/
theorem complete_chord_sets_eq_of_le_three {n : ℕ} (hn : n ≤ 3)
    (S T : Finset (Edge (completeDiagram n).area))
    (hS : S ⊆ completeChordPositions n) (hT : T ⊆ completeChordPositions n)
    (hcard : S.card = T.card) : S = T := by
  have hsingle (e f : Edge (completeDiagram n).area)
      (he : e ∈ completeChordPositions n) (hf : f ∈ completeChordPositions n) : e = f := by
    have he' := (mem_completeChordPositions n e).mp he
    have hf' := (mem_completeChordPositions n f).mp hf
    have heb := e.head.isLt
    have hfb := f.head.isLt
    apply (completeDiagram n).endpointEmbedding.injective
    exact Prod.ext (show e.tail = f.tail from Fin.ext (by lia))
      (show e.head = f.head from Fin.ext (by lia))
  by_cases hSe : S = ∅
  · subst S
    have hTe : T = ∅ := Finset.card_eq_zero.mp (by simpa using hcard.symm)
    exact hTe.symm
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have hTne : T.Nonempty := Finset.card_pos.mp (by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨e, he⟩)
    obtain ⟨f, hf⟩ := hTne
    ext g
    constructor
    · intro hg
      exact (hsingle g f (hS hg) (hT hf)).symm ▸ hf
    · intro hg
      exact (hsingle g e (hT hg) (hS he)).symm ▸ he

/-- The complete active-layer theorem for greatest label at most three. -/
theorem complete_reachable_of_le_three {n : ℕ} (hn : n ≤ 3)
    (θ η : Orientation (completeDiagram n))
    (hθ : SelectedConnected θ) (hcθ : Cover θ 0 (Fin.last n))
    (hη : SelectedConnected η) (hcη : Cover η 0 (Fin.last n))
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  have hnpos : 0 < n := hcθ.1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  obtain ⟨α, hθα, hrowα, hchainα⟩ := exists_complete_chain k θ hcθ hθ
  obtain ⟨β, hηβ, hrowβ, hchainβ⟩ := exists_complete_chain k η hcη hη
  have hcount : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hηβ))
  have hcard : (selectedCompleteChords α).card = (selectedCompleteChords β).card := by
    have hα := totalSelected_eq_chain_add_chords α hrowα hchainα
    have hβ := totalSelected_eq_chain_add_chords β hrowβ hchainβ
    lia
  have hsets := complete_chord_sets_eq_of_le_three hn
    (selectedCompleteChords α) (selectedCompleteChords β)
    (selectedCompleteChords_subset α) (selectedCompleteChords_subset β) hcard
  have hαβ : α = β := by
    rw [eq_completeChainState_of_chain α hrowα hchainα,
      eq_completeChainState_of_chain β hrowβ hchainβ, hsets]
  have reverse {σ τ : Orientation (completeDiagram (k + 1))}
      (h : Relation.ReflTransGen (Flip (completeDiagram (k + 1))) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram (k + 1))) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  exact hθα.trans (hαβ.symm ▸ reverse hηβ)

end VerticalStripLLT.Circular.DiagramProof

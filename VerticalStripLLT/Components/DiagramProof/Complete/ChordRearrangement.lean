import VerticalStripLLT.Components.DiagramProof.Complete.ChordExchange
import VerticalStripLLT.Components.DiagramProof.Relations.FixedPositionPaths

/-! Rearrange all chords except the outer chord by smaller complete-interval paths. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Assuming smaller active-layer connectivity, equal-size chord sets with the
same outer chord membership connect by actual flips. -/
theorem completeChainState_reachable_of_fixed_outer {n : ℕ} (hn : 5 ≤ n)
    (hsmaller : ∀ k, k < n → ∀ α β : Orientation (completeDiagram k),
      SelectedConnected α → Cover α 0 (Fin.last k) →
      SelectedConnected β → Cover β 0 (Fin.last k) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram k)) α β)
    (S T : Finset (Edge (completeDiagram n).area))
    (hS : S ⊆ completeChordPositions n) (hT : T ⊆ completeChordPositions n)
    (hcard : S.card = T.card)
    (houter : completeOuterChord n (by lia) ∈ S ↔ completeOuterChord n (by lia) ∈ T) :
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n S) (completeChainState n T) := by
  let p := completeOuterChord n (by lia)
  let step := fun X Y : Finset (Edge (completeDiagram n).area) =>
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n X) (completeChainState n Y)
  have hpJ : p ∉ completeChordLeft n := completeOuterChord_not_mem_left _
  have hpK : p ∉ completeChordRight n := completeOuterChord_not_mem_right _
  have hcover : ∀ e, e ∈ completeChordPositions n → e ≠ p →
      e ∈ completeChordLeft n ∨ e ∈ completeChordRight n := by
    intro e he hne
    apply completeChordPositions_mem_left_or_right_of_ne_outer he
    intro hout
    exact hne ((eq_completeOuterChord_iff _ e).mpr hout)
  have hoverlap : (completeChordLeft n ∩ completeChordRight n).Nonempty := by
    obtain ⟨e, heL, heR⟩ := completeChordPositions_common_mem n hn
    exact ⟨e, Finset.mem_inter.mpr ⟨heL, heR⟩⟩
  have hpaths : Relation.ReflTransGen step S T := by
    apply fixed_card_connectivity_fixing_position
      (completeChordPositions n) (completeChordLeft n) (completeChordRight n) p step
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hpJ hpK hcover hoverlap
      ?_ hS hT hcard houter
    intro X e f hX hlocal he hf
    have hfp : f ≠ p := by
      intro h
      rcases hlocal with hl | hr
      · exact hpJ (h ▸ hl.2)
      · exact hpK (h ▸ hr.2)
    have heX := Finset.mem_of_mem_erase he
    have hfX : f ∉ X := fun h => hf (Finset.mem_erase.mpr ⟨hfp, h⟩)
    have hpath := completeChainState_exchange_in_two_intervals hn hsmaller
      X hX e f heX hfX hlocal
    exact ⟨insert f (X.erase e), Relation.ReflTransGen.single hpath, rfl⟩
  have flatten {X Y : Finset (Edge (completeDiagram n).area)}
      (h : Relation.ReflTransGen step X Y) :
      Relation.ReflTransGen (Flip (completeDiagram n))
        (completeChainState n X) (completeChainState n Y) := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.trans hstep
  exact flatten hpaths

/-- The same rearrangement theorem applies to actual chain states without choosing a new model. -/
theorem complete_chain_reachable_of_fixed_outer {n : ℕ} (hn : 5 ≤ n)
    (hsmaller : ∀ k, k < n → ∀ α β : Orientation (completeDiagram k),
      SelectedConnected α → Cover α 0 (Fin.last k) →
      SelectedConnected β → Cover β 0 (Fin.last k) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram k)) α β)
    (θ η : Orientation (completeDiagram n))
    (hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n)
    (hchainθ : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (hchainη : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v)
    (htotal : totalSelected θ = totalSelected η)
    (houter : completeOuterChord n (by lia) ∈ fullSelection θ ↔
      completeOuterChord n (by lia) ∈ fullSelection η) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  have hcard : (selectedCompleteChords θ).card = (selectedCompleteChords η).card := by
    have hθ := totalSelected_eq_chain_add_chords θ hrowθ hchainθ
    have hη := totalSelected_eq_chain_add_chords η hrowη hchainη
    lia
  have houter' : completeOuterChord n (by lia) ∈ selectedCompleteChords θ ↔
      completeOuterChord n (by lia) ∈ selectedCompleteChords η := by
    simp only [selectedCompleteChords, Finset.mem_inter, completeOuterChord_mem, and_true]
    exact houter
  have hp := completeChainState_reachable_of_fixed_outer hn hsmaller
    (selectedCompleteChords θ) (selectedCompleteChords η)
    (selectedCompleteChords_subset θ) (selectedCompleteChords_subset η) hcard houter'
  rw [← eq_completeChainState_of_chain θ hrowθ hchainθ,
    ← eq_completeChainState_of_chain η hrowη hchainη] at hp
  exact hp

end

end VerticalStripLLT.Circular.DiagramProof

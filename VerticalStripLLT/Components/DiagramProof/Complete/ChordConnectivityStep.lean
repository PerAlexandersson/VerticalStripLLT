import VerticalStripLLT.Components.DiagramProof.Complete.ChordRearrangement
import VerticalStripLLT.Components.DiagramProof.Complete.ChordOuterExchange
import VerticalStripLLT.Components.DiagramProof.Complete.ChordSubsetChoice
import VerticalStripLLT.Components.DiagramProof.Complete.SingleChord
import VerticalStripLLT.Components.DiagramProof.Complete.Chain

/-! The complete-diagram chord induction step, including changes of the outer chord. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Assuming connectivity for smaller complete diagrams, all equal-size chord sets
connect on a complete diagram with greatest vertex at least five. -/
theorem completeChainState_reachable_of_smaller {n : ℕ} (hn : 5 ≤ n)
    (hsmaller : ∀ k, k < n → ∀ α β : Orientation (completeDiagram k),
      SelectedConnected α → Cover α 0 (Fin.last k) →
      SelectedConnected β → Cover β 0 (Fin.last k) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram k)) α β)
    (S T : Finset (Edge (completeDiagram n).area))
    (hS : S ⊆ completeChordPositions n) (hT : T ⊆ completeChordPositions n)
    (hcard : S.card = T.card) :
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n S) (completeChainState n T) := by
  let p := completeOuterChord n (by lia)
  let i : Fin (n + 1) := ⟨1, by lia⟩
  let j : Fin (n + 1) := ⟨2, by lia⟩
  let t : Fin (n + 1) := ⟨3, by lia⟩
  let a : Edge (completeDiagram n).area := completeEdge n i t (by change 1 < 3; decide)
  let b : Edge (completeDiagram n).area := completeEdge n j (Fin.last n) (by change 2 < n; lia)
  have hat : a.tail.val = 1 := by simp [a, i]
  have hah : a.head.val = 3 := rfl
  have hbt : b.tail.val = 2 := by simp [b, j]
  have hbh : b.head.val = n := rfl
  have hpt : p.tail.val = 1 := completeOuterChord_tail_val n _
  have hph : p.head.val = n := completeOuterChord_head_val n _
  have haU : a ∈ completeChordPositions n := by
    rw [mem_completeChordPositions, hat, hah]
    decide
  have hbU : b ∈ completeChordPositions n := by
    rw [mem_completeChordPositions, hbt, hbh]
    constructor <;> lia
  have hpU : p ∈ completeChordPositions n := completeOuterChord_mem n _
  have hap : a ≠ p := by
    intro h
    have := congrArg (fun e : Edge (completeDiagram n).area => e.head.val) h
    rw [hah, hph] at this
    lia
  have hbp : b ≠ p := by
    intro h
    have := congrArg (fun e : Edge (completeDiagram n).area => e.tail.val) h
    rw [hbt, hpt] at this
    lia
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun e : Edge (completeDiagram n).area => e.tail.val) h
    rw [hat, hbt] at this
    lia
  have fixed (X Y : Finset (Edge (completeDiagram n).area))
      (hX : X ⊆ completeChordPositions n) (hY : Y ⊆ completeChordPositions n)
      (hc : X.card = Y.card) (hp : p ∈ X ↔ p ∈ Y) :
      Relation.ReflTransGen (Flip (completeDiagram n))
        (completeChainState n X) (completeChainState n Y) :=
    completeChainState_reachable_of_fixed_outer hn hsmaller X Y hX hY hc hp
  have join (X Y : Finset (Edge (completeDiagram n).area))
      (hX : X ⊆ completeChordPositions n) (hY : Y ⊆ completeChordPositions n)
      (hc : X.card = Y.card) (hpX : p ∉ X) (hpY : p ∈ Y) :
      Relation.ReflTransGen (Flip (completeDiagram n))
        (completeChainState n X) (completeChainState n Y) := by
    have hpos : 0 < X.card := by
      rw [hc]
      exact Finset.card_pos.mpr ⟨p, hpY⟩
    by_cases hone : X.card = 1
    · have haSub : ({a} : Finset _) ⊆ completeChordPositions n :=
        Finset.singleton_subset_iff.mpr haU
      have hpSub : ({p} : Finset _) ⊆ completeChordPositions n :=
        Finset.singleton_subset_iff.mpr hpU
      have hfirst := fixed X {a} hX haSub (by simpa using hone)
        (by simp [hpX, hap.symm])
      have hmiddle := completeChainState_singleChord_reachable (by lia) a p hat hah hpt hph
      have hlast := fixed {p} Y hpSub hY (by simpa [← hc] using hone.symm)
        (by simp [hpY])
      exact hfirst.trans (hmiddle.trans hlast)
    · have htwo : 2 ≤ X.card := by lia
      obtain ⟨Z, hZU, hpZ, haZ, hbZ, hZcard⟩ :=
        exists_subset_with_prescribed_pair_away_from (completeChordPositions n) X p a b
          haU hbU hap hbp hab hX hpX htwo
      let W := insert p (Z.erase a)
      have hWU : W ⊆ completeChordPositions n := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hpU
        · exact hZU (Finset.mem_of_mem_erase he)
      have hWcard : W.card = Y.card := by
        have hpErase : p ∉ Z.erase a := fun h => hpZ (Finset.mem_of_mem_erase h)
        change (insert p (Z.erase a)).card = Y.card
        rw [Finset.card_insert_of_notMem hpErase, Finset.card_erase_of_mem haZ]
        lia
      have hfirst := fixed X Z hX hZU hZcard.symm (by simp [hpX, hpZ])
      have hmiddle := completeChainState_outerChord_reachable (by lia) Z hZU a b
        hat hah hbt hbh haZ hbZ hpZ
      have hlast := fixed W Y hWU hY hWcard (by simp [W, hpY])
      exact hfirst.trans (hmiddle.trans hlast)
  have reverse {σ τ : Orientation (completeDiagram n)}
      (h : Relation.ReflTransGen (Flip (completeDiagram n)) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram n)) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  by_cases hpS : p ∈ S
  · by_cases hpT : p ∈ T
    · exact fixed S T hS hT hcard (by simp [hpS, hpT])
    · exact reverse (join T S hT hS hcard.symm hpT hpS)
  · by_cases hpT : p ∈ T
    · exact join S T hS hT hcard hpS hpT
    · exact fixed S T hS hT hcard (by simp [hpS, hpT])

/-- Normalize both connected active states to chains and apply the chord induction step. -/
theorem complete_reachable_of_smaller {n : ℕ} (hn : 5 ≤ n)
    (hsmaller : ∀ k, k < n → ∀ α β : Orientation (completeDiagram k),
      SelectedConnected α → Cover α 0 (Fin.last k) →
      SelectedConnected β → Cover β 0 (Fin.last k) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram k)) α β)
    (θ η : Orientation (completeDiagram n))
    (hθ : SelectedConnected θ) (hcθ : Cover θ 0 (Fin.last n))
    (hη : SelectedConnected η) (hcη : Cover η 0 (Fin.last n))
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  obtain ⟨α, hθα, hrowα, hchainα⟩ := exists_complete_chain k θ hcθ hθ
  obtain ⟨β, hηβ, hrowβ, hchainβ⟩ := exists_complete_chain k η hcη hη
  have hαβcount : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hηβ))
  have hcard : (selectedCompleteChords α).card = (selectedCompleteChords β).card := by
    have hα := totalSelected_eq_chain_add_chords α hrowα hchainα
    have hβ := totalSelected_eq_chain_add_chords β hrowβ hchainβ
    lia
  have hαβ := completeChainState_reachable_of_smaller hn hsmaller
    (selectedCompleteChords α) (selectedCompleteChords β)
    (selectedCompleteChords_subset α) (selectedCompleteChords_subset β) hcard
  rw [← eq_completeChainState_of_chain α hrowα hchainα,
    ← eq_completeChainState_of_chain β hrowβ hchainβ] at hαβ
  have reverse {σ τ : Orientation (completeDiagram (k + 1))}
      (h : Relation.ReflTransGen (Flip (completeDiagram (k + 1))) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram (k + 1))) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  exact hθα.trans (hαβ.trans (reverse hηβ))

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.Complete.Chords
import VerticalStripLLT.Components.DiagramProof.Complete.IntervalCounts
import VerticalStripLLT.Components.DiagramProof.Complete.ChordIntervals

/-! Actual exchange of two chords supported inside a smaller complete interval. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Agreement of chord sets outside the embedded diagram gives full selected agreement there. -/
theorem completeChainState_outside_of_chords {k n : ℕ}
    (ι : Fin (k + 1) ↪o Fin (n + 1))
    (S T : Finset (Edge (completeDiagram n).area))
    (hout : ∀ e, (¬ ∃ a b, ι a = e.tail ∧ ι b = e.head) → (e ∈ S ↔ e ∈ T))
    (u v : Fin (n + 1)) (huv : ¬ ∃ a b, ι a = u ∧ ι b = v) :
    (completeDiagram n).edgeData.selected (completeChainState n S).val u v ↔
      (completeDiagram n).edgeData.selected (completeChainState n T).val u v := by
  have hfull (e : Edge (completeDiagram n).area) (ht : e.tail = u) (hh : e.head = v) :
      e ∈ fullSelection (completeChainState n S) ↔
        e ∈ fullSelection (completeChainState n T) := by
    rw [completeChainState_fullSelection, completeChainState_fullSelection]
    simp only [Finset.mem_union]
    rw [hout e (by simpa only [ht, hh] using huv)]
  constructor
  · rintro ⟨e, he, ht, hh⟩
    exact ⟨e, (hfull e ht hh).mp he, ht, hh⟩
  · rintro ⟨e, he, ht, hh⟩
    exact ⟨e, (hfull e ht hh).mpr he, ht, hh⟩

/-- Exchange two chord positions in one interval using its smaller active-layer theorem. -/
theorem completeChainState_exchange_in_interval {n a m : ℕ}
    (ha : 0 < a) (hb : a + m ≤ n)
    (hsmall : ∀ α β : Orientation (completeDiagram (m + 1)),
      SelectedConnected α → Cover α 0 (Fin.last (m + 1)) →
      SelectedConnected β → Cover β 0 (Fin.last (m + 1)) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram (m + 1))) α β)
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n)
    (e f : Edge (completeDiagram n).area) (he : e ∈ S) (hf : f ∉ S)
    (hfc : f ∈ completeChordPositions n)
    (heinside : ∃ i j,
      intervalEmbed a m ha hb i = e.tail ∧ intervalEmbed a m ha hb j = e.head)
    (hfinside : ∃ i j,
      intervalEmbed a m ha hb i = f.tail ∧ intervalEmbed a m ha hb j = f.head) :
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n S) (completeChainState n (insert f (S.erase e))) := by
  have hn : 0 < n := by lia
  have hT : insert f (S.erase e) ⊆ completeChordPositions n := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact hfc
    · exact hS (Finset.mem_of_mem_erase hg)
  apply complete_interval_chain_path_of_equal_count ha hb hsmall
    (completeChainState n S) (completeChainState n (insert f (S.erase e)))
    (completeChainState_row hn S hS) (completeChainState_row hn _ hT)
    (completeChainState_chain S) (completeChainState_chain _) ?_ ?_
  · rw [completeChainState_totalSelected S hS, completeChainState_totalSelected _ hT]
    have hf' : f ∉ S.erase e := fun h => hf (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hf', Finset.card_erase_of_mem he]
    have hpos := Finset.card_pos.mpr ⟨e, he⟩
    lia
  · apply completeChainState_outside_of_chords
    intro g hg
    have hge : g ≠ e := fun h => hg (h.symm ▸ heinside)
    have hgf : g ≠ f := fun h => hg (h.symm ▸ hfinside)
    constructor
    · intro hgS
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hge, hgS⟩)
    · intro hgT
      exact (Finset.mem_erase.mp ((Finset.mem_insert.mp hgT).resolve_left hgf)).2

/-- Either of the two smaller complete intervals supplies a chord exchange. -/
theorem completeChainState_exchange_in_two_intervals {n : ℕ} (hn : 5 ≤ n)
    (hsmaller : ∀ k, k < n → ∀ α β : Orientation (completeDiagram k),
      SelectedConnected α → Cover α 0 (Fin.last k) →
      SelectedConnected β → Cover β 0 (Fin.last k) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram k)) α β)
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n)
    (e f : Edge (completeDiagram n).area) (he : e ∈ S) (hf : f ∉ S)
    (hlocal : (e ∈ completeChordLeft n ∧ f ∈ completeChordLeft n) ∨
      (e ∈ completeChordRight n ∧ f ∈ completeChordRight n)) :
    Relation.ReflTransGen (Flip (completeDiagram n))
      (completeChainState n S) (completeChainState n (insert f (S.erase e))) := by
  have hn2 : 2 ≤ n := by lia
  have hlt : n - 2 + 1 < n := by lia
  rcases hlocal with ⟨heL, hfL⟩ | ⟨heR, hfR⟩
  · exact completeChainState_exchange_in_interval (a := 1) (m := n - 2)
      (by decide) (by lia) (hsmaller _ hlt) S hS e f he hf
      ((mem_completeChordLeft n f).mp hfL).1
      (completeChordLeft_exists_interval_endpoints hn2 heL)
      (completeChordLeft_exists_interval_endpoints hn2 hfL)
  · exact completeChainState_exchange_in_interval (a := 2) (m := n - 2)
      (by decide) (by lia) (hsmaller _ hlt) S hS e f he hf
      ((mem_completeChordRight n f).mp hfR).1
      (completeChordRight_exists_interval_endpoints hn2 heR)
      (completeChordRight_exists_interval_endpoints hn2 hfR)

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.OuterChordMove
import VerticalStripLLT.Components.DiagramProof.ChainStateSelection
import VerticalStripLLT.Components.DiagramProof.ChordIntervals

/-! Express the proved outer-chord move as an exact exchange of chord sets. -/

namespace VerticalStripLLT.Circular.DiagramProof

set_option backward.isDefEq.respectTransparency false

/-- The outer move on chord sets exchanges `13` for `1n`, provided `2n` is present. -/
theorem completeChainState_outerChord_reachable {n : ℕ} (hn : 4 ≤ n)
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n)
    (a b : Edge (completeDiagram n).area)
    (hat : a.tail.val = 1) (hah : a.head.val = 3)
    (hbt : b.tail.val = 2) (hbh : b.head.val = n)
    (ha : a ∈ S) (hb : b ∈ S) (hp : completeOuterChord n (by lia) ∉ S) :
    Relation.ReflTransGen (Flip (completeDiagram n)) (completeChainState n S)
      (completeChainState n (insert (completeOuterChord n (by lia)) (S.erase a))) := by
  classical
  let θ := completeChainState n S
  let p := completeOuterChord n (by lia)
  have hpt : p.tail = a.tail := Fin.ext (by
    change (completeOuterChord n _).tail.val = a.tail.val
    rw [completeOuterChord_tail_val, hat])
  have hph : p.head = Fin.last n := Fin.ext (completeOuterChord_head_val n _)
  have hbn : b.head = Fin.last n := Fin.ext hbh
  have h13 : (completeDiagram n).edgeData.selected θ.val a.tail a.head := by
    apply (mem_fullSelection_iff_selected θ a).mp
    rw [completeChainState_fullSelection]
    exact Finset.mem_union_right _ ha
  have h2n : (completeDiagram n).edgeData.selected θ.val b.tail (Fin.last n) := by
    rw [← hbn]
    apply (mem_fullSelection_iff_selected θ b).mp
    rw [completeChainState_fullSelection]
    exact Finset.mem_union_right _ hb
  have hpC : p ∈ completeChordPositions n := completeOuterChord_mem n _
  have h1n : ¬ (completeDiagram n).edgeData.selected θ.val a.tail (Fin.last n) := by
    intro hs
    have hmem : p ∈ fullSelection θ :=
      (mem_fullSelection_iff_selected θ p).mpr (by simpa only [hpt, hph] using hs)
    rw [completeChainState_fullSelection] at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact Finset.disjoint_left.mp (completeChainEdges_disjoint_chords n) hmem hpC
    · exact hp hmem
  obtain ⟨η, hpath, hη⟩ := exists_complete_outerChordMove θ a.tail b.tail a.head
    hat hbt hah (by change a.head.val < n; lia)
    (completeChainState_row (by lia) S hS) (completeChainState_chain S) h13 h2n h1n
  have heq : η = completeChainState n (insert p (S.erase a)) := by
    apply fullSelection_injective
    ext e
    rw [mem_fullSelection_iff_selected η e, hη,
      ← mem_fullSelection_iff_selected θ e, completeChainState_fullSelection,
      completeChainState_fullSelection]
    have hep : (e.tail = a.tail ∧ e.head = Fin.last n) ↔ e = p := by
      constructor
      · rintro ⟨ht, hh⟩
        exact (completeDiagram n).endpointEmbedding.injective
          (Prod.ext (ht.trans hpt.symm) (hh.trans hph.symm))
      · rintro rfl
        exact ⟨hpt, hph⟩
    have hea : (e.tail = a.tail ∧ e.head = a.head) ↔ e = a := by
      constructor
      · rintro ⟨ht, hh⟩
        exact (completeDiagram n).endpointEmbedding.injective (Prod.ext ht hh)
      · rintro rfl; exact ⟨rfl, rfl⟩
    have haC : a ∉ completeChainEdges n := fun h =>
      Finset.disjoint_left.mp (completeChainEdges_disjoint_chords n) h (hS ha)
    rw [hep, hea]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    clear hη
    grind only
  exact heq ▸ hpath

end VerticalStripLLT.Circular.DiagramProof

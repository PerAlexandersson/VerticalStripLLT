import VerticalStripLLT.Components.DiagramProof.CompleteDiagram
import VerticalStripLLT.Components.DiagramProof.ChainConnected

/-! A complete chain and its selected chords, in the existing orientation type. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Chords join positive vertices and skip at least one vertex. -/
def completeChordPositions (n : ℕ) : Finset (Edge (completeDiagram n).area) :=
  Finset.univ.filter fun e => 0 < e.tail.val ∧ e.tail.val + 1 < e.head.val

@[simp]
theorem mem_completeChordPositions (n : ℕ) (e : Edge (completeDiagram n).area) :
    e ∈ completeChordPositions n ↔ 0 < e.tail.val ∧ e.tail.val + 1 < e.head.val := by
  simp only [completeChordPositions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The extreme root edge and the consecutive edges between positive vertices. -/
def completeChainEdges (n : ℕ) : Finset (Edge (completeDiagram n).area) :=
  Finset.univ.filter fun e => (e.tail = 0 ∧ e.head = Fin.last n) ∨
    (0 < e.tail.val ∧ e.tail.val + 1 = e.head.val)

@[simp]
theorem mem_completeChainEdges (n : ℕ) (e : Edge (completeDiagram n).area) :
    e ∈ completeChainEdges n ↔ (e.tail = 0 ∧ e.head = Fin.last n) ∨
      (0 < e.tail.val ∧ e.tail.val + 1 = e.head.val) := by
  simp only [completeChainEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Select a fixed chain and any specified additional edges. -/
def completeChainState (n : ℕ) (S : Finset (Edge (completeDiagram n).area)) :
    Orientation (completeDiagram n) :=
  ofFullSelection (complete_forward n) (completeChainEdges n ∪ S) (by simp)

@[simp]
theorem completeChainState_fullSelection (n : ℕ)
    (S : Finset (Edge (completeDiagram n).area)) :
    fullSelection (completeChainState n S) = completeChainEdges n ∪ S :=
  fullSelection_ofFullSelection ..

theorem completeChainEdges_disjoint_chords (n : ℕ) :
    Disjoint (completeChainEdges n) (completeChordPositions n) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  obtain ⟨hpos, hskip⟩ := (mem_completeChordPositions n e).mp hc
  rcases (mem_completeChainEdges n e).mp he with ⟨ht, _⟩ | ⟨_, hstep⟩
  · rw [ht] at hpos
    exact (Nat.lt_irrefl 0 hpos)
  · lia

/-- The selected chords of a state, without its fixed chain edges. -/
def selectedCompleteChords {n : ℕ} (θ : Orientation (completeDiagram n)) :
    Finset (Edge (completeDiagram n).area) :=
  fullSelection θ ∩ completeChordPositions n

@[simp]
theorem selectedCompleteChords_chainState {n : ℕ}
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n) :
    selectedCompleteChords (completeChainState n S) = S := by
  have hdis := completeChainEdges_disjoint_chords n
  ext e
  simp only [selectedCompleteChords, completeChainState_fullSelection,
    Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨he | he, hc⟩
    · exact (Finset.disjoint_left.mp hdis he hc).elim
    · exact he
  · intro he
    exact ⟨Or.inr he, hS he⟩

theorem completeChainState_totalSelected {n : ℕ}
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n) :
    totalSelected (completeChainState n S) = (completeChainEdges n).card + S.card := by
  rw [totalSelected, completeChainState_fullSelection]
  exact Finset.card_union_of_disjoint ((completeChainEdges_disjoint_chords n).mono_right hS)

/-- A chain with only chords added has exactly its extreme edge out of zero. -/
theorem completeChainState_row {n : ℕ} (hn : 0 < n)
    (S : Finset (Edge (completeDiagram n).area)) (hS : S ⊆ completeChordPositions n)
    (v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (completeChainState n S).val 0 v ↔
      v = Fin.last n := by
  constructor
  · rintro ⟨e, he, ht, hh⟩
    change e.tail = 0 at ht
    change e.head = v at hh
    change e ∈ fullSelection (completeChainState n S) at he
    rw [completeChainState_fullSelection] at he
    rcases Finset.mem_union.mp he with he | he
    · rcases (mem_completeChainEdges n e).mp he with ⟨_, htop⟩ | ⟨hpos, _⟩
      · exact hh.symm.trans htop
      · rw [ht] at hpos
        exact (Nat.lt_irrefl 0 hpos).elim
    · have hpos := ((mem_completeChordPositions n e).mp (hS he)).1
      rw [ht] at hpos
      exact (Nat.lt_irrefl 0 hpos).elim
  · rintro rfl
    let e := completeCornerEdge n hn
    have he : e ∈ fullSelection (completeChainState n S) := by
      rw [completeChainState_fullSelection]
      apply Finset.mem_union_left
      exact (mem_completeChainEdges n e).mpr (Or.inl
        ⟨completeCornerEdge_tail n hn, completeCornerEdge_head n hn⟩)
    exact ⟨e, he, completeCornerEdge_tail n hn, completeCornerEdge_head n hn⟩

theorem completeChainState_chain {n : ℕ} (S : Finset (Edge (completeDiagram n).area))
    (u v : Fin (n + 1)) (hu : 0 < u) (huv : u.val + 1 = v.val) :
    (completeDiagram n).edgeData.selected (completeChainState n S).val u v := by
  have hlt : u < v := by change u.val < v.val; lia
  let e := completeEdge n u v hlt
  have he : e ∈ fullSelection (completeChainState n S) := by
    rw [completeChainState_fullSelection]
    apply Finset.mem_union_left
    apply (mem_completeChainEdges n e).mpr
    right
    change 0 < (completeEdge n u v hlt).tail.val ∧
      (completeEdge n u v hlt).tail.val + 1 = (completeEdge n u v hlt).head.val
    rw [completeEdge_tail, completeEdge_head]
    exact ⟨hu, huv⟩
  exact ⟨e, he, completeEdge_tail n u v hlt, completeEdge_head n u v hlt⟩

/-- The root-row and chain conditions determine a state from its selected chords. -/
theorem eq_completeChainState_of_chain {n : ℕ} (θ : Orientation (completeDiagram n))
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v) :
    θ = completeChainState n (selectedCompleteChords θ) := by
  apply fullSelection_injective
  ext e
  rw [completeChainState_fullSelection]
  constructor
  · intro he
    by_cases hzero : e.tail = 0
    · have hsel := (mem_fullSelection_iff_selected θ e).mp he
      rw [hzero, hrow] at hsel
      exact Finset.mem_union_left _ ((mem_completeChainEdges n e).mpr
        (Or.inl ⟨hzero, hsel⟩))
    · have hpos : 0 < e.tail.val := Fin.pos_iff_ne_zero.mpr hzero
      by_cases hadj : e.tail.val + 1 = e.head.val
      · exact Finset.mem_union_left _ ((mem_completeChainEdges n e).mpr
          (Or.inr ⟨hpos, hadj⟩))
      · have hlt : e.tail.val < e.head.val := complete_forward n e
        apply Finset.mem_union_right
        exact Finset.mem_inter.mpr ⟨he, (mem_completeChordPositions n e).mpr ⟨hpos, by lia⟩⟩
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · apply (mem_fullSelection_iff_selected θ e).mpr
      rcases (mem_completeChainEdges n e).mp he with ⟨ht, hh⟩ | ⟨hpos, hadj⟩
      · rw [ht, hrow]
        exact hh
      · exact hchain e.tail e.head hpos hadj
    · exact (Finset.mem_inter.mp he).1

theorem selectedCompleteChords_subset {n : ℕ} (θ : Orientation (completeDiagram n)) :
    selectedCompleteChords θ ⊆ completeChordPositions n := Finset.inter_subset_right

/-- In any chain state the selected-edge count is the fixed chain count plus chord count. -/
theorem totalSelected_eq_chain_add_chords {n : ℕ} (θ : Orientation (completeDiagram n))
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v) :
    totalSelected θ = (completeChainEdges n).card + (selectedCompleteChords θ).card :=
  (congrArg totalSelected (eq_completeChainState_of_chain θ hrow hchain)).trans
    (completeChainState_totalSelected _ (selectedCompleteChords_subset θ))

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.CompleteChords
import VerticalStripLLT.Components.DiagramProof.CompleteInterval

/-!
# The two overlapping chord intervals

The chord positions of the complete diagram are covered by the two complete
intervals on `0,1,...,n-1` and `0,2,...,n`, apart from the outer chord `1n`.
This file records only the finite position bookkeeping; it introduces no
state space or additional component notion.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Chord positions whose head is below the top vertex. -/
def completeChordLeft (n : ℕ) : Finset (Edge (completeDiagram n).area) :=
  (completeChordPositions n).filter (fun e => e.head.val < n)

/-- Chord positions whose tail is at least the second internal vertex. -/
def completeChordRight (n : ℕ) : Finset (Edge (completeDiagram n).area) :=
  (completeChordPositions n).filter (fun e => 2 ≤ e.tail.val)

@[simp]
theorem mem_completeChordLeft (n : ℕ) (e : Edge (completeDiagram n).area) :
    e ∈ completeChordLeft n ↔
      e ∈ completeChordPositions n ∧ e.head.val < n := by
  simp only [completeChordLeft, Finset.mem_filter]

@[simp]
theorem mem_completeChordRight (n : ℕ) (e : Edge (completeDiagram n).area) :
    e ∈ completeChordRight n ↔
      e ∈ completeChordPositions n ∧ 2 ≤ e.tail.val := by
  simp only [completeChordRight, Finset.mem_filter]

/-- Every chord other than `1n` lies in one of the two interval position sets. -/
theorem completeChordPositions_mem_left_or_right_of_ne_outer
    {n : ℕ} {e : Edge (completeDiagram n).area}
    (he : e ∈ completeChordPositions n)
    (houter : ¬ (e.tail.val = 1 ∧ e.head.val = n)) :
    e ∈ completeChordLeft n ∨ e ∈ completeChordRight n := by
  have hchord := (mem_completeChordPositions n e).mp he
  by_cases hhead : e.head.val < n
  · exact Or.inl ((mem_completeChordLeft n e).mpr ⟨he, hhead⟩)
  · have hhead_eq : e.head.val = n := by
      have hhead_le : e.head.val ≤ n := by
        exact Nat.le_of_lt_succ e.head.isLt
      lia
    have htail_ge : 2 ≤ e.tail.val := by
      by_contra htail
      have htail_eq : e.tail.val = 1 := by
        have htail_pos := hchord.1
        lia
      exact houter ⟨htail_eq, hhead_eq⟩
    exact Or.inr ((mem_completeChordRight n e).mpr ⟨he, htail_ge⟩)

/-- A pointwise form of the preceding cover, with the outer chord included. -/
theorem completeChordPositions_mem_outer_or_left_or_right
    {n : ℕ} {e : Edge (completeDiagram n).area}
    (he : e ∈ completeChordPositions n) :
    (e.tail.val = 1 ∧ e.head.val = n) ∨
      e ∈ completeChordLeft n ∨ e ∈ completeChordRight n := by
  by_cases houter : e.tail.val = 1 ∧ e.head.val = n
  · exact Or.inl houter
  · exact Or.inr (completeChordPositions_mem_left_or_right_of_ne_outer he houter)

/-- The two interval sets have the common position `24` once `n ≥ 5`. -/
theorem completeChordPositions_common_mem (n : ℕ) (hn : 5 ≤ n) :
    ∃ e, e ∈ completeChordLeft n ∧ e ∈ completeChordRight n := by
  let i : Fin (n + 1) := ⟨2, by lia⟩
  let j : Fin (n + 1) := ⟨4, by lia⟩
  let e : Edge (completeDiagram n).area := completeEdge n i j (by
    change 2 < 4
    norm_num)
  have he : e ∈ completeChordPositions n := by
    apply (mem_completeChordPositions n e).mpr
    change 0 < (completeEdge n i j _).tail.val ∧
      (completeEdge n i j _).tail.val + 1 < (completeEdge n i j _).head.val
    rw [completeEdge_tail, completeEdge_head]
    exact ⟨by change 0 < 2; decide, by change 2 + 1 < 4; decide⟩
  have heleft : e ∈ completeChordLeft n :=
    (mem_completeChordLeft n e).mpr ⟨he, by change 4 < n; lia⟩
  have heright : e ∈ completeChordRight n :=
    (mem_completeChordRight n e).mpr ⟨he, by
      change 2 ≤ (completeEdge n i j _).tail.val
      rw [completeEdge_tail]⟩
  exact ⟨e, heleft, heright⟩

/-! Endpoint witnesses in the two interval embeddings. -/

theorem completeChordLeft_exists_interval_endpoints
    {n : ℕ} (hn : 2 ≤ n) {e : Edge (completeDiagram n).area}
    (he : e ∈ completeChordLeft n) :
    ∃ u v : Fin (n - 2 + 2),
      intervalEmbed 1 (n - 2) (by lia) (by lia) u = e.tail ∧
      intervalEmbed 1 (n - 2) (by lia) (by lia) v = e.head := by
  have he' := (mem_completeChordLeft n e).mp he
  have hchord := (mem_completeChordPositions n e).mp he'.1
  have htail_lo : 1 ≤ e.tail.val := by lia
  have htail_hi : e.tail.val ≤ 1 + (n - 2) := by
    have hhead_lt : e.head.val < n := he'.2
    lia
  have hhead_lo : 1 ≤ e.head.val := by
    have htail_pos := hchord.1
    have hgap := hchord.2
    lia
  have hhead_hi : e.head.val ≤ 1 + (n - 2) := by
    have hhead_lt : e.head.val < n := he'.2
    lia
  obtain ⟨u, hu⟩ :=
    (intervalEmbed_range (n := n) (a := 1) (m := n - 2) (by lia) (by lia)
      e.tail).mpr (Or.inr ⟨htail_lo, htail_hi⟩)
  obtain ⟨v, hv⟩ :=
    (intervalEmbed_range (n := n) (a := 1) (m := n - 2) (by lia) (by lia)
      e.head).mpr (Or.inr ⟨hhead_lo, hhead_hi⟩)
  exact ⟨u, v, hu, hv⟩

theorem completeChordRight_exists_interval_endpoints
    {n : ℕ} (hn : 2 ≤ n) {e : Edge (completeDiagram n).area}
    (he : e ∈ completeChordRight n) :
    ∃ u v : Fin (n - 2 + 2),
      intervalEmbed 2 (n - 2) (by lia) (by lia) u = e.tail ∧
      intervalEmbed 2 (n - 2) (by lia) (by lia) v = e.head := by
  have he' := (mem_completeChordRight n e).mp he
  have hchord := (mem_completeChordPositions n e).mp he'.1
  have htail_lo : 2 ≤ e.tail.val := he'.2
  have htail_hi : e.tail.val ≤ 2 + (n - 2) := by
    have htail_lt := e.tail.isLt
    lia
  have hhead_lo : 2 ≤ e.head.val := by
    have hgap := hchord.2
    have htail_ge := hchord.1
    lia
  have hhead_hi : e.head.val ≤ 2 + (n - 2) := by
    have hhead_lt := e.head.isLt
    lia
  obtain ⟨u, hu⟩ :=
    (intervalEmbed_range (n := n) (a := 2) (m := n - 2) (by lia) (by lia)
      e.tail).mpr (Or.inr ⟨htail_lo, htail_hi⟩)
  obtain ⟨v, hv⟩ :=
    (intervalEmbed_range (n := n) (a := 2) (m := n - 2) (by lia) (by lia)
      e.head).mpr (Or.inr ⟨hhead_lo, hhead_hi⟩)
  exact ⟨u, v, hu, hv⟩

/-- The chord from the first positive vertex to the greatest vertex. -/
def completeOuterChord (n : ℕ) (hn : 3 ≤ n) : Edge (completeDiagram n).area :=
  completeEdge n ⟨1, by lia⟩ (Fin.last n) (by change 1 < n; lia)

@[simp]
theorem completeOuterChord_tail_val (n : ℕ) (hn : 3 ≤ n) :
    (completeOuterChord n hn).tail.val = 1 := by
  unfold completeOuterChord
  rw [completeEdge_tail]

@[simp]
theorem completeOuterChord_head_val (n : ℕ) (hn : 3 ≤ n) :
    (completeOuterChord n hn).head.val = n := rfl

theorem completeOuterChord_mem (n : ℕ) (hn : 3 ≤ n) :
    completeOuterChord n hn ∈ completeChordPositions n := by
  rw [mem_completeChordPositions, completeOuterChord_tail_val, completeOuterChord_head_val]
  constructor <;> lia

theorem eq_completeOuterChord_iff {n : ℕ} (hn : 3 ≤ n)
    (e : Edge (completeDiagram n).area) :
    e = completeOuterChord n hn ↔ e.tail.val = 1 ∧ e.head.val = n := by
  constructor
  · rintro rfl
    exact ⟨completeOuterChord_tail_val n hn, completeOuterChord_head_val n hn⟩
  · rintro ⟨ht, hh⟩
    apply (completeDiagram n).endpointEmbedding.injective
    apply Prod.ext
    · exact Fin.ext (ht.trans (completeOuterChord_tail_val n hn).symm)
    · exact Fin.ext (hh.trans (completeOuterChord_head_val n hn).symm)

theorem completeOuterChord_not_mem_left {n : ℕ} (hn : 3 ≤ n) :
    completeOuterChord n hn ∉ completeChordLeft n := by
  intro h
  have hlt := ((mem_completeChordLeft n _).mp h).2
  rw [completeOuterChord_head_val] at hlt
  exact (Nat.lt_irrefl n hlt)

theorem completeOuterChord_not_mem_right {n : ℕ} (hn : 3 ≤ n) :
    completeOuterChord n hn ∉ completeChordRight n := by
  intro h
  have hle := ((mem_completeChordRight n _).mp h).2
  rw [completeOuterChord_tail_val] at hle
  lia

end

end VerticalStripLLT.Circular.DiagramProof

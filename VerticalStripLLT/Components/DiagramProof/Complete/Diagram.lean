import VerticalStripLLT.Components.IntervalDiagram
import VerticalStripLLT.Components.DiagramProof.Corners.CornerChains
import VerticalStripLLT.Circular.EdgeLength
import Mathlib.Tactic.Linarith

/-!
# The complete natural diagram

The parameter `n` is the largest vertex label, so this file works on the
vertices `0, ..., n`.  Its area sequence is `a j = j`; consequently every
forward pair is represented by one natural edge.  The edge `0n` is the only
maximal corner when `0 < n`.

This is deliberately a small geometric interface.  It does not introduce a
new state or component model; states and flips continue to use the ordinary
`Diagram` APIs.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- The area sequence of the complete natural diagram on `0, ..., n`. -/
def completeArea (n : ℕ) : CircularArea (n + 1) where
  positive := Nat.succ_pos n
  area := fun j => j.val
  bound := by
    intro j
    exact j.isLt
  cyclic := by
    intro j
    change (j.val + 1) % (n + 1) ≤ j.val + 1
    by_cases hj : j.val < n
    · rw [Nat.mod_eq_of_lt (by lia : j.val + 1 < n + 1)]
    · have hjn : j.val = n := by
        have hlt := j.isLt
        lia
      rw [hjn, Nat.mod_self]
      exact Nat.zero_le _

@[simp]
theorem completeArea_area (n : ℕ) (j : Fin (n + 1)) :
    (completeArea n).area j = j.val := rfl

/-- The undecorated complete natural diagram on `0, ..., n`. -/
def completeDiagram (n : ℕ) : Diagram (n + 1) where
  area := completeArea n
  strict := ∅
  strict_corner := by simp

@[simp]
theorem completeDiagram_strict (n : ℕ) : (completeDiagram n).strict = ∅ := rfl

/-- The edge with prescribed forward endpoints in the complete diagram. -/
def completeEdge (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    Edge (completeArea n) :=
  ⟨(j, ⟨j.val - i.val, (Nat.sub_le _ _).trans_lt j.isLt⟩), by
    constructor
    · have hij' : i.val < j.val := hij
      exact Nat.sub_pos_of_lt hij'
    · change j.val - i.val ≤ j.val
      exact Nat.sub_le _ _⟩

@[simp]
theorem completeEdge_head (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    (completeEdge n i j hij).head = j := rfl

@[simp]
theorem completeEdge_length (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    (completeEdge n i j hij).length.val = j.val - i.val := rfl

@[simp]
theorem completeEdge_tail (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    (completeEdge n i j hij).tail = i := by
  apply Fin.ext
  change (j.val + (n + 1) - (j.val - i.val)) % (n + 1) = i.val
  have hsum : j.val + (n + 1) - (j.val - i.val) = i.val + (n + 1) := by
    lia
  rw [hsum, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/-- Every edge of the complete diagram is forward. -/
theorem complete_forward (n : ℕ) (e : Edge (completeDiagram n).area) :
    e.tail < e.head := by
  have hlen : e.length.val ≤ e.head.val := by
    exact e.length_le_area
  have hpos : 0 < e.length.val := e.length_pos
  have htail : e.tail.val = e.head.val - e.length.val := by
    change (e.head.val + (n + 1) - e.length.val) % (n + 1) = _
    have hsum : e.head.val + (n + 1) - e.length.val =
        (e.head.val - e.length.val) + (n + 1) := by
      lia
    rw [hsum, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt e.head.isLt)
  change e.tail.val < e.head.val
  rw [htail]
  lia

/-- Every forward pair occurs, with the canonical edge above it. -/
theorem complete_naturalEdge_iff (n : ℕ) (i j : Fin (n + 1)) :
    (∃ e : Edge (completeDiagram n).area,
      e.tail = i ∧ e.head = j) ↔ i < j := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact complete_forward n e
  · intro hij
    exact ⟨completeEdge n i j hij, completeEdge_tail n i j hij,
      completeEdge_head n i j hij⟩

private theorem edge_eq_of_endpoints {n : ℕ} {A : CircularArea n}
    {e f : Edge A} (ht : e.tail = f.tail) (hh : e.head = f.head) : e = f := by
  apply Subtype.ext
  apply Prod.ext
  · exact hh
  · apply Fin.ext
    exact Edge.length_eq_of_endpoints (e := f) (f := e) ht hh

/-- Any edge is the canonical edge determined by its endpoints. -/
theorem completeEdge_eq_of_endpoints (n : ℕ) (e : Edge (completeDiagram n).area) :
    completeEdge n e.tail e.head (complete_forward n e) = e := by
  apply edge_eq_of_endpoints
  · exact completeEdge_tail n e.tail e.head (complete_forward n e)
  · rfl

/-- The marked maximal edge `0n`, available for a nontrivial diagram. -/
def completeCornerEdge (n : ℕ) (hn : 0 < n) :
  Edge (completeDiagram n).area :=
  completeEdge n 0 (Fin.last n) (by
    change 0 < n
    exact hn)

@[simp]
theorem completeCornerEdge_tail (n : ℕ) (hn : 0 < n) :
    (completeCornerEdge n hn).tail = 0 := by
  exact completeEdge_tail n 0 (Fin.last n) _

@[simp]
theorem completeCornerEdge_head (n : ℕ) (hn : 0 < n) :
    (completeCornerEdge n hn).head = Fin.last n := by
  rfl

theorem completeCornerEdge_isCorner (n : ℕ) (hn : 0 < n) :
    IsCorner (completeCornerEdge n hn) := by
  constructor
  · change (Fin.last n).val - (0 : Fin (n + 1)).val =
      (Fin.last n).val
    simp
  · change ((completeArea n).next (Fin.last n)).val ≤ (Fin.last n).val
    rw [CircularArea.next_val]
    simp

/-- The maximal-corner characterization of the complete diagram. -/
theorem complete_isCorner_iff (n : ℕ) (hn : 0 < n)
    (e : Edge (completeDiagram n).area) :
    IsCorner e ↔ e = completeCornerEdge n hn := by
  constructor
  · intro he
    have hlen : e.length.val = e.head.val := by
      simpa [completeDiagram, completeArea] using he.1
    have htail : e.tail = 0 := by
      apply Fin.ext
      change (e.head.val + (n + 1) - e.length.val) % (n + 1) = 0
      have hsum : e.head.val + (n + 1) - e.length.val = n + 1 := by
        rw [hlen]
        simp
      rw [hsum, Nat.mod_self]
    have hhead : e.head = Fin.last n := by
      apply Fin.ext
      have hle : e.head.val ≤ n := Nat.lt_succ_iff.mp e.head.isLt
      by_contra hhead_ne
      have hne : e.head.val ≠ n := by
        intro h
        apply hhead_ne
        exact h
      have hlt : e.head.val < n := lt_of_le_of_ne hle hne
      have hnext : e.head.val + 1 ≤ e.head.val := by
        have hmod : (e.head.val + 1) % (n + 1) = e.head.val + 1 :=
          Nat.mod_eq_of_lt (by lia)
        have hc := he.2
        change (e.head.val + 1) % (n + 1) ≤ e.head.val at hc
        rw [hmod] at hc
        exact hc
      lia
    apply edge_eq_of_endpoints
    · exact htail.trans (completeCornerEdge_tail n hn).symm
    · exact hhead.trans (completeCornerEdge_head n hn).symm
  · intro he
    rw [he]
    exact completeCornerEdge_isCorner n hn

/-- The maximal-corner set is the singleton `{0n}`. -/
theorem complete_maximalCorners (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter IsCorner : Finset (Edge (completeDiagram n).area)) =
      {completeCornerEdge n hn} := by
  ext e
  simp [complete_isCorner_iff n hn e]

/-- Mark the unique maximal corner in the complete diagram. -/
def completeCornerDiagram (n : ℕ) (hn : 0 < n) : Diagram (n + 1) :=
  (completeDiagram n).strictify (completeCornerEdge n hn)
    (completeCornerEdge_isCorner n hn)

@[simp]
theorem completeCornerDiagram_strict (n : ℕ) (hn : 0 < n) :
    (completeCornerDiagram n hn).strict = {completeCornerEdge n hn} := by
  change insert (completeCornerEdge n hn) ∅ = {completeCornerEdge n hn}
  exact Finset.insert_empty

end

end VerticalStripLLT.Circular.DiagramProof

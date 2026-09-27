import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Circular.EdgeBounds
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Forward diagrams from interval-closed relations

The predecessor interval of a vertex starts at its least predecessor, or at the
vertex itself when there are no predecessors. Subtracting this boundary from the
vertex rank gives a circular area sequence with no wrapping edges. Edge lengths
in this new diagram are rank differences, not distances in any original lift.
-/

namespace VerticalStripLLT.Circular.Diagram

open Classical

noncomputable section

variable {n : ℕ}

/-- Include the vertex itself so that the lower boundary is defined for an empty row. -/
def intervalCandidates (R : Fin n → Fin n → Prop) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i = j ∨ R i j

theorem intervalCandidates_nonempty (R : Fin n → Fin n → Prop) (j : Fin n) :
    (intervalCandidates R j).Nonempty := by
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩

/-- The first predecessor, with the vertex itself as the empty-row boundary. -/
def intervalLeft (R : Fin n → Fin n → Prop) (j : Fin n) : Fin n :=
  (intervalCandidates R j).min' (intervalCandidates_nonempty R j)

theorem intervalLeft_mem (R : Fin n → Fin n → Prop) (j : Fin n) :
    intervalLeft R j = j ∨ R (intervalLeft R j) j := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (intervalCandidates R j) (intervalCandidates_nonempty R j))).2

theorem intervalLeft_le (R : Fin n → Fin n → Prop) (j : Fin n) :
    intervalLeft R j ≤ j := by
  exact Finset.min'_le (intervalCandidates R j) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩)

theorem intervalLeft_le_of_rel {R : Fin n → Fin n → Prop} {i j : Fin n}
    (h : R i j) : intervalLeft R j ≤ i := by
  exact Finset.min'_le (intervalCandidates R j) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩)

variable (R : Fin n → Fin n → Prop)
variable (hforward : ∀ {i j : Fin n}, R i j → i < j)
variable (hinterval : ∀ {i j k : Fin n}, R i k → i < j → j < k → R i j ∧ R j k)

include hforward hinterval in
/-- Interval closure makes each row exactly the interval above its lower boundary. -/
theorem rel_iff_intervalLeft {i j : Fin n} :
    R i j ↔ intervalLeft R j ≤ i ∧ i < j := by
  constructor
  · intro h
    exact ⟨intervalLeft_le_of_rel h, hforward h⟩
  · rintro ⟨hleft, hij⟩
    rcases intervalLeft_mem R j with heq | hrel
    · rw [heq] at hleft
      exact False.elim ((not_lt_of_ge hleft) hij)
    · rcases lt_or_eq_of_le hleft with hlt | heq
      · exact (hinterval hrel hlt hij).2
      · simpa only [heq] using hrel

include hinterval in
/-- Lower boundaries are weakly increasing along the finite vertex order. -/
theorem intervalLeft_monotone : Monotone (intervalLeft R) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · by_cases hli : intervalLeft R j < i
    · rcases intervalLeft_mem R j with heq | hrel
      · rw [heq] at hli
        exact False.elim ((not_lt_of_ge hij.le) hli)
      · exact intervalLeft_le_of_rel ((hinterval hrel hli hij).1)
    · exact (intervalLeft_le R i).trans (le_of_not_gt hli)
  · exact le_rfl

/-- The width of the predecessor interval, measured in ranks. -/
def intervalArea (j : Fin n) : ℕ := j.val - (intervalLeft R j).val

theorem intervalArea_le (j : Fin n) : intervalArea R j ≤ j.val := Nat.sub_le _ _

include hinterval in
theorem intervalArea_cyclic (hn : 0 < n) (i : Fin n) :
    intervalArea R ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ ≤ intervalArea R i + 1 := by
  let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
  change intervalArea R j ≤ intervalArea R i + 1
  by_cases hnext : i.val + 1 < n
  · have hj : j.val = i.val + 1 := Nat.mod_eq_of_lt hnext
    have hij : i ≤ j := by change i.val ≤ j.val; lia
    have hleft : (intervalLeft R i).val ≤ (intervalLeft R j).val :=
      intervalLeft_monotone R hinterval hij
    have hli : (intervalLeft R i).val ≤ i.val := intervalLeft_le R i
    have hlj : (intervalLeft R j).val ≤ j.val := intervalLeft_le R j
    change j.val - (intervalLeft R j).val ≤ i.val - (intervalLeft R i).val + 1
    calc
      j.val - (intervalLeft R j).val ≤ j.val - (intervalLeft R i).val :=
        Nat.sub_le_sub_left hleft _
      _ = i.val - (intervalLeft R i).val + 1 := by
        rw [hj, Nat.add_comm i.val 1, Nat.add_sub_assoc hli, Nat.add_comm]

  · have hnxt : i.val + 1 = n := by have := i.isLt; lia
    have hj : j.val = 0 := by dsimp [j]; rw [hnxt, Nat.mod_self]
    simp only [intervalArea, hj, Nat.zero_sub]
    exact Nat.zero_le _

/-- The actual undecorated circular diagram realizing a forward interval relation. -/
def ofIntervalRelation (hn : 0 < n) : Diagram n where
  area := {
    positive := hn
    area := intervalArea R
    bound := fun j => (intervalArea_le R j).trans_lt j.isLt
    cyclic := intervalArea_cyclic R hinterval hn
  }
  strict := ∅
  strict_corner := by intro e he; simp at he

@[simp]
theorem ofIntervalRelation_strict (hn : 0 < n) :
    (ofIntervalRelation R hinterval hn).strict = ∅ := rfl

theorem ofIntervalRelation_area_le_head (hn : 0 < n) (j : Fin n) :
    (ofIntervalRelation R hinterval hn).area.area j ≤ j.val := intervalArea_le R j

/-- The rank interval construction has no wrapping natural edges. -/
theorem ofIntervalRelation_tail_val (hn : 0 < n)
    (e : Edge (ofIntervalRelation R hinterval hn).area) :
    e.tail.val = e.head.val - e.length.val := by
  have hlen : e.length.val ≤ e.head.val :=
    e.length_le_area.trans (ofIntervalRelation_area_le_head R hinterval hn e.head)
  have hsub : e.head.val + n - e.length.val = (e.head.val - e.length.val) + n := by
    lia
  change (e.head.val + n - e.length.val) % n = e.head.val - e.length.val
  rw [hsub, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt e.head.isLt)

include hforward in
theorem ofIntervalRelation_edge_rel (hn : 0 < n)
    (e : Edge (ofIntervalRelation R hinterval hn).area) : R e.tail e.head := by
  apply (rel_iff_intervalLeft R hforward hinterval).mpr
  have htail := ofIntervalRelation_tail_val R hinterval hn e
  have hlen : e.length.val ≤ e.head.val - (intervalLeft R e.head).val :=
    e.length_le_area
  have hleft : (intervalLeft R e.head).val ≤ e.head.val := intervalLeft_le R e.head
  have hpos := e.length_pos
  constructor
  · change (intervalLeft R e.head).val ≤ e.tail.val
    lia
  · change e.tail.val < e.head.val
    lia

include hforward in
/-- All natural edges of the constructed diagram point forward in rank order. -/
theorem ofIntervalRelation_forward (hn : 0 < n)
    (e : Edge (ofIntervalRelation R hinterval hn).area) : e.tail < e.head :=
  hforward (ofIntervalRelation_edge_rel R hforward hinterval hn e)

include hforward in
/-- The constructed natural graph realizes the relation exactly. -/
theorem ofIntervalRelation_naturalEdge_iff (hn : 0 < n) (i j : Fin n) :
    (∃ e : Edge (ofIntervalRelation R hinterval hn).area,
      e.tail = i ∧ e.head = j) ↔ R i j := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact ofIntervalRelation_edge_rel R hforward hinterval hn e
  · intro hij
    have hij' : i.val < j.val := hforward hij
    have hleft : (intervalLeft R j).val ≤ i.val := intervalLeft_le_of_rel hij
    let e : Edge (ofIntervalRelation R hinterval hn).area :=
      ⟨(j, ⟨j.val - i.val, (Nat.sub_le _ _).trans_lt j.isLt⟩), by
        constructor
        · exact Nat.sub_pos_of_lt hij'
        · change j.val - i.val ≤ j.val - (intervalLeft R j).val
          lia⟩
    refine ⟨e, ?_, rfl⟩
    apply Fin.ext
    rw [ofIntervalRelation_tail_val R hinterval hn e]
    change j.val - (j.val - i.val) = i.val
    lia

end

end VerticalStripLLT.Circular.Diagram

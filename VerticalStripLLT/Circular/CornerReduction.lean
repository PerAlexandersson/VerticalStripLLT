import VerticalStripLLT.Circular.CornerDeleteOrientation
import VerticalStripLLT.Circular.ZeroAreaExpansion
import VerticalStripLLT.Circular.StrictCycleVanishing

/-! Conditional reduction to all-corners-strict diagrams; the base hypothesis remains unproved. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Diagram

variable {n : ℕ}

theorem card_edge_deleteCorner_lt (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    Fintype.card (Edge (D.deleteCorner e he).area) < Fintype.card (Edge D.area) :=
  Fintype.card_lt_of_injective_of_notMem (D.cornerIncl e he) (D.cornerIncl_injective e he)
    (b := e) (by rintro ⟨f, hf⟩; exact D.cornerIncl_ne e he f hf)

theorem card_normal_strictify_lt (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) :
    (D.strictify e he).edgeData.normalEdges.card < D.edgeData.normalEdges.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨e, (mem_normalEdges_iff D e).mpr hns, ?_⟩
    rw [mem_normalEdges_iff]
    exact fun h => h (Finset.mem_insert_self e D.strict)
  · intro f hf
    rw [mem_normalEdges_iff] at hf ⊢
    exact fun h => hf (Finset.mem_insert_of_mem h)

end Diagram

/-- The expansion follows from the all-corners-strict case by corner deletion–contraction. -/
theorem expansion_of_cornerReduction {n : ℕ}
    (hbase : ∀ D : Diagram n, (∀ e : Edge D.area, IsCorner e → e ∈ D.strict) →
      ∀ m : ℕ, xQShift m (D.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion D))
    (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  induction h : Fintype.card (Edge D.area) ^ 2 + D.edgeData.normalEdges.card
    using Nat.strong_induction_on generalizing D with
  | _ k ih =>
    by_cases hc : ∃ e : Edge D.area, IsCorner e ∧ e ∉ D.strict
    · obtain ⟨e, he, hns⟩ := hc
      rw [D.xQShift_coloringLLT_corner e he hns, D.shiftedOrientationExpansion_corner e he hns,
        map_add, map_mul, evalElementary_C]
      have h1 : Fintype.card (Edge (D.strictify e he).area) ^ 2 +
          (D.strictify e he).edgeData.normalEdges.card < k := by
        have := D.card_normal_strictify_lt e he hns
        rw [← h]
        change Fintype.card (Edge D.area) ^ 2 + _ < _
        lia
      have h2 : Fintype.card (Edge (D.deleteCorner e he).area) ^ 2 +
          (D.deleteCorner e he).edgeData.normalEdges.card < k := by
        have hlt := D.card_edge_deleteCorner_lt e he
        have hle : (D.deleteCorner e he).edgeData.normalEdges.card ≤
            Fintype.card (Edge (D.deleteCorner e he).area) := Finset.card_le_univ _
        rw [← h]
        set a := Fintype.card (Edge (D.deleteCorner e he).area)
        set b := Fintype.card (Edge D.area)
        have : a * a + a < b * b := by nlinarith
        nlinarith
      rw [ih _ h1 _ rfl, ih _ h2 _ rfl]
    · push Not at hc
      exact hbase D hc m

/-- Only acyclic strict relations with some normal edge remain after the proved reductions. -/
theorem expansion_of_strictCorners_positive {n : ℕ}
    (hremaining : ∀ D : Diagram n,
      (∀ e : Edge D.area, IsCorner e → e ∈ D.strict) →
      D.edgeData.Admissible ∅ → D.edgeData.normalEdges.Nonempty →
      ∀ m : ℕ, xQShift m (D.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion D))
    (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  classical
  apply expansion_of_cornerReduction (D := D) (m := m)
  intro D hc m
  by_cases ha : D.edgeData.Admissible ∅
  · by_cases hn : D.edgeData.normalEdges.Nonempty
    · exact hremaining D hc ha hn m
    · exact coloringLLT_shifted_eq_expansion_of_no_normal D
        (Finset.not_nonempty_iff_eq_empty.mp hn) m
  · exact coloringLLT_shifted_eq_expansion_of_not_admissible_empty D ha m

end VerticalStripLLT.Circular

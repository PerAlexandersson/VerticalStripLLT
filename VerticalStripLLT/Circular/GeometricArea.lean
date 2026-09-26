import VerticalStripLLT.Circular.DNRealization
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Doubled half-square area and its preservation by the actual neutral move. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- Each strict corner contributes half a square rather than a full square. -/
noncomputable def doubledArea : ℕ := 2 * (∑ i, D.area.area i) - D.strict.card

theorem strict_card_le_area_sum : D.strict.card ≤ ∑ i, D.area.area i := by
  have hinj : Set.InjOn Edge.head (D.strict : Set (Edge D.area)) := by
    intro e he f hf hh
    exact D.strict_edge_eq_of_head_eq he hf hh
  calc
    D.strict.card = (D.strict.image Edge.head).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = ∑ i ∈ D.strict.image Edge.head, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ D.strict.image Edge.head, D.area.area i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
      exact corner_area_pos (D.strict_corner e he)
    _ ≤ ∑ i, D.area.area i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; lia)

/-- The natural-valued statistic agrees with twice the geometric half-square area. -/
theorem doubledArea_int : (D.doubledArea : ℤ) =
    2 * (∑ i, (D.area.area i : ℤ)) - D.strict.card := by
  have hh := D.strict_card_le_area_sum
  have hle : D.strict.card ≤ 2 * (∑ i, D.area.area i) := by lia
  simp only [doubledArea, Int.natCast_sub hle, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sum]

theorem area_sum_eq_of_two_row_update (D' : Diagram n) (i j : Fin n)
    (hne : i ≠ j) (hpos : 0 < D.area.area j)
    (hupdate : D'.area.area = Function.update
      (Function.update D.area.area i (D.area.area i + 1)) j (D.area.area j - 1)) :
    ∑ v, D'.area.area v = ∑ v, D.area.area v := by
  have hp (v : Fin n) : D'.area.area v + (if v = j then 1 else 0) =
      D.area.area v + (if v = i then 1 else 0) := by
    rw [hupdate]
    by_cases hvj : v = j
    · subst v
      simp only [Function.update_self, Ne.symm hne, ↓reduceIte]
      lia
    · rw [Function.update_of_ne hvj]
      by_cases hvi : v = i
      · subst v
        simp only [Function.update_self, hne, ↓reduceIte]
      · rw [Function.update_of_ne hvi]
        simp only [hvj, hvi, ↓reduceIte]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun v _ => hp v)
  simp only [Finset.sum_add_distrib] at hs
  simpa using hs

end Diagram

namespace FullNeutralBounce

variable {n : ℕ} {D D' : Diagram n} (B : FullNeutralBounce D D')

include B

theorem strict_card_eq (ha : D.edgeData.Admissible ∅) : D'.strict.card = D.strict.card := by
  have hh := Fintype.card_congr (B.edgeEquiv ha)
  simpa only [Diagram.StrictEdge, Fintype.card_coe] using hh.symm

theorem doubledArea_eq (ha : D.edgeData.Admissible ∅)
    (harea : ∑ v, D'.area.area v = ∑ v, D.area.area v) :
    D'.doubledArea = D.doubledArea := by
  unfold Diagram.doubledArea
  rw [harea, B.strict_card_eq ha]

end FullNeutralBounce

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The full DN branch preserves half-square area and strictly lowers the secondary rank. -/
theorem exists_area_preserving_dn {t x : ℤ} (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (h : ReverseBounce D t x)
    (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    ∃ D' : Diagram n, Nonempty (FullNeutralBounce D D') ∧
      D'.edgeData.Admissible ∅ ∧ D'.doubledArea = D.doubledArea ∧
      D'.strictRank < D.strictRank := by
  obtain ⟨B⟩ := ReverseBounce.exists_indexed_contacts D h ht.1 hx
  obtain ⟨D', ⟨C⟩, hupdate, ha', hrank⟩ :=
    D.exists_fullNeutralBounce_of_reverseBounce ha ht h hx hx1
  have hfirst : D.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := by
    rw [D.residue_succ]
    exact D.strict_zero_gap_area_eq hx h.terminal_gap.1
  have hsum := D.area_sum_eq_of_two_row_update D' (D.residue (x + 1)) (D.residue t)
    (B.next_residue_ne ha ht hx1) (by have := ht.2.1; lia) (by rwa [hfirst])
  exact ⟨D', ⟨C⟩, ha', C.doubledArea_eq ha hsum, hrank⟩

end Diagram
end VerticalStripLLT.Circular

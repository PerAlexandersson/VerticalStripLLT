import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Data.Int.Interval

/-! Maximal vertices in a bounded integer reachability relation. -/

namespace VerticalStripLLT.Circular

/-- Reachable vertices in the finite interval from `z` through `z + B`. -/
noncomputable def reachableVertices (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    Finset ℤ := by
  classical
  exact (Finset.Icc z (z + (B : ℤ))).filter (Relation.ReflTransGen S z)

theorem self_mem_reachableVertices (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    z ∈ reachableVertices S B z := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    exact ⟨le_rfl, le_add_of_nonneg_right (Int.natCast_nonneg B)⟩
  · exact Relation.ReflTransGen.refl

theorem reachableVertices_nonempty (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    (reachableVertices S B z).Nonempty :=
  ⟨z, self_mem_reachableVertices S B z⟩

theorem mem_reachableVertices_iff (S : ℤ → ℤ → Prop) (B : ℕ) (z w : ℤ) :
    w ∈ reachableVertices S B z ↔
      z ≤ w ∧ w ≤ z + (B : ℤ) ∧ Relation.ReflTransGen S z w := by
  classical
  simp only [reachableVertices, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hzw, hwB⟩, hw⟩
    exact ⟨hzw, hwB, hw⟩
  · rintro ⟨hzw, hwB, hw⟩
    exact ⟨⟨hzw, hwB⟩, hw⟩

/-- The largest reachable vertex in the bounded interval. -/
noncomputable def reachableMaximum (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) : ℤ :=
  (reachableVertices S B z).max' (reachableVertices_nonempty S B z)

theorem maximum_mem_reachableVertices (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    reachableMaximum S B z ∈ reachableVertices S B z := by
  exact Finset.max'_mem _ _

theorem maximum_reachable (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    Relation.ReflTransGen S z (reachableMaximum S B z) := by
  exact ((mem_reachableVertices_iff S B z (reachableMaximum S B z)).mp
    (maximum_mem_reachableVertices S B z)).2.2

theorem z_le_maximum (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    z ≤ reachableMaximum S B z := by
  exact Finset.le_max' _ z (self_mem_reachableVertices S B z)

theorem maximum_le (S : ℤ → ℤ → Prop) (B : ℕ) (z : ℤ) :
    reachableMaximum S B z ≤ z + (B : ℤ) := by
  exact ((mem_reachableVertices_iff S B z (reachableMaximum S B z)).mp
    (maximum_mem_reachableVertices S B z)).2.1

/-- Any reachable vertex satisfying the supplied forward span bound is below the maximum. -/
theorem reachable_le_maximum (S : ℤ → ℤ → Prop) (B : ℕ) (z w : ℤ)
    (hbound : ∀ u, Relation.ReflTransGen S z u → z ≤ u ∧ u - z ≤ (B : ℤ))
    (hw : Relation.ReflTransGen S z w) : w ≤ reachableMaximum S B z := by
  apply Finset.le_max'
  apply (mem_reachableVertices_iff S B z w).mpr
  exact ⟨(hbound w hw).1, by have := (hbound w hw).2; lia, hw⟩

end VerticalStripLLT.Circular

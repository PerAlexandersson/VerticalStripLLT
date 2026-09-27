import VerticalStripLLT.Components.BlockExtractor
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Cancellation of signed increasing/decreasing block words. -/

namespace VerticalStripLLT.Components

open scoped BigOperators
open Classical

noncomputable section

variable {V : Type*} [LinearOrder V]

omit [LinearOrder V] in
private theorem sum_powerset_pow_neg_one (s : Finset V) :
    ∑ T ∈ s.powerset, (-1 : ℤ) ^ T.card =
      if s.Nonempty then 0 else 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℤ) 1 s
  simp only [one_pow, mul_one] at h
  rw [h]
  simp only [neg_add_cancel]
  by_cases hs : s.Nonempty
  · simp [hs, Finset.card_ne_zero.mpr hs]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

omit [LinearOrder V] in
private theorem sum_powerset_filter_forall (A : Finset V) (p : V → Prop)
    [DecidablePred p] (f : Finset V → ℤ) :
    (∑ T ∈ A.powerset, if ∀ x ∈ T, p x then f T else 0) =
      ∑ T ∈ (A.filter p).powerset, f T := by
  rw [← Finset.sum_filter]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hT, hp⟩ u hu
    exact Finset.mem_filter.mpr ⟨hT hu, hp u hu⟩
  · intro h
    exact ⟨fun u hu => (Finset.mem_filter.mp (h hu)).1,
      fun u hu => (Finset.mem_filter.mp (h hu)).2⟩

theorem blockCancellation (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B A : Finset V) (hA : A ⊆ B) :
    (∑ T ∈ A.powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible R (blockWord B T) then 1 else 0)) =
      if (∀ u ∈ A, ¬sinkOn R B u) then 1 else 0 := by
  classical
  let p : V → Prop := sinkOn R B
  have hcompat (T : Finset V) (hT : T ⊆ A) :
      wordCompatible R (blockWord B T) ↔ ∀ u ∈ T, p u := by
    exact blockWord_compatible_iff_forall_sink R hinc B T (hT.trans hA)
  rw [show (∑ T ∈ A.powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible R (blockWord B T) then 1 else 0)) =
      ∑ T ∈ A.powerset,
        (if ∀ u ∈ T, p u then (-1 : ℤ) ^ T.card else 0) by
    apply Finset.sum_congr rfl
    intro T hT
    rw [hcompat T (Finset.mem_powerset.mp hT)]
    split_ifs <;> simp]
  rw [sum_powerset_filter_forall A p (fun T => (-1 : ℤ) ^ T.card)]
  rw [sum_powerset_pow_neg_one]
  change (if (A.filter p).Nonempty then 0 else 1) =
    if ∀ u ∈ A, ¬p u then 1 else 0
  by_cases hS : (A.filter p).Nonempty
  · have hnot : ¬∀ u ∈ A, ¬p u := by
      intro h
      obtain ⟨u, hu⟩ := hS
      exact (h u (Finset.mem_filter.mp hu).1) (Finset.mem_filter.mp hu).2
    rw [ite_eq_left hS, ite_eq_right hnot]
  · have hall : ∀ u ∈ A, ¬p u := by
      intro u hu huS
      exact hS ⟨u, Finset.mem_filter.mpr ⟨hu, huS⟩⟩
    rw [ite_eq_right hS, ite_eq_left hall]

theorem blockCancellation_erase (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) (r : V) :
    (∑ T ∈ (B.erase r).powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible R (blockWord B T) then 1 else 0)) =
      if (∀ u ∈ B.erase r, ¬sinkOn R B u) then 1 else 0 := by
  exact blockCancellation R hinc B (B.erase r) (Finset.erase_subset _ _)

/-- For a block with maximum `r`, the signed coefficient detects its unique sink. -/
theorem blockCancellation_uniqueSink (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) (r : V)
    (hr : r ∈ B) (hmax : ∀ u ∈ B, u ≤ r) :
    (∑ T ∈ (B.erase r).powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible R (blockWord B T) then 1 else 0)) =
      if (∀ u ∈ B, sinkOn R B u ↔ u = r) then 1 else 0 := by
  rw [blockCancellation_erase R hinc B r]
  have hrsink : sinkOn R B r :=
    ⟨hr, fun u hu hRu => (not_lt_of_ge (hmax u hu)) (hinc hRu)⟩
  congr 1
  apply propext
  constructor
  · intro h u hu
    constructor
    · intro hs
      by_contra hne
      exact h u (Finset.mem_erase.mpr ⟨hne, hu⟩) hs
    · rintro rfl
      exact hrsink
  · intro h u hu hs
    exact (Finset.mem_erase.mp hu).1 ((h u (Finset.mem_erase.mp hu).2).mp hs)

end

end VerticalStripLLT.Components

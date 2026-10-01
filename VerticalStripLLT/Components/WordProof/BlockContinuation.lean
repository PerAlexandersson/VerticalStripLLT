import VerticalStripLLT.Components.WordProof.BlockFullWords
import VerticalStripLLT.Components.WordProof.BlockCancellation

/-! Exact support and signed cancellation for a first mountain and its continuation. -/

namespace VerticalStripLLT.Components

open Classical
open scoped BigOperators

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- A word enumerates the specified finite support exactly once. -/
def fullOn (S : Finset V) (w : List V) : Prop :=
  w.Nodup ∧ ∀ v, v ∈ w ↔ v ∈ S

omit [LinearOrder V] in
@[simp]
theorem fullOn_nil (S : Finset V) : fullOn S [] ↔ S = ∅ := by
  simp only [fullOn, List.nodup_nil, List.not_mem_nil, false_iff, true_and]
  exact Finset.eq_empty_iff_forall_notMem.symm

omit [LinearOrder V] in
@[simp]
theorem fullOn_univ [Fintype V] (w : List V) :
    fullOn Finset.univ w ↔ fullWord w := by
  simp [fullOn, fullWord]

/-- Removing the first block leaves exactly the complementary support. -/
theorem fullOn_blockWord_append_iff (S B T : Finset V) (hT : T ⊆ B) (w : List V) :
    fullOn S (blockWord B T ++ w) ↔ B ⊆ S ∧ fullOn (S \ B) w := by
  constructor
  · rintro ⟨hnodup, hmem⟩
    obtain ⟨_, hw, hdis⟩ := List.nodup_append.mp hnodup
    refine ⟨?_, hw, ?_⟩
    · intro v hv
      exact (hmem v).mp (List.mem_append_left _ ((mem_blockWord_iff B T hT v).mpr hv))
    · intro v
      constructor
      · intro hv
        refine Finset.mem_sdiff.mpr ⟨(hmem v).mp (List.mem_append_right _ hv), ?_⟩
        intro hvB
        exact hdis v ((mem_blockWord_iff B T hT v).mpr hvB) v hv rfl
      · intro hv
        obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.mp hv
        rcases List.mem_append.mp ((hmem v).mpr hvS) with hblock | hw
        · exact (hvB ((mem_blockWord_iff B T hT v).mp hblock)).elim
        · exact hw
  · rintro ⟨hBS, hw, hmem⟩
    refine ⟨List.Nodup.append (blockWord_nodup B T hT) hw ?_, ?_⟩
    · intro v hblock htail
      exact (Finset.mem_sdiff.mp ((hmem v).mp htail)).2
        ((mem_blockWord_iff B T hT v).mp hblock)
    · intro v
      rw [List.mem_append, mem_blockWord_iff B T hT, hmem]
      constructor
      · rintro (hB | hSB)
        · exact hBS hB
        · exact (Finset.mem_sdiff.mp hSB).1
      · intro hv
        by_cases hB : v ∈ B
        · exact Or.inl hB
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨hv, hB⟩)

/-- The crossing condition is independent of the chosen decreasing tail. -/
theorem fullOn_compatible_blockWord_append_iff
    (R : V → V → Prop) (S B T : Finset V) (hT : T ⊆ B) (w : List V) :
    (fullOn S (blockWord B T ++ w) ∧ wordCompatible R (blockWord B T ++ w)) ↔
      B ⊆ S ∧ fullOn (S \ B) w ∧ wordCompatible R (blockWord B T) ∧
        wordCompatible R w ∧ ∀ x ∈ S \ B, ∀ y ∈ B, ¬ R x y := by
  rw [fullOn_blockWord_append_iff S B T hT w, wordCompatible_append_iff]
  constructor
  · rintro ⟨⟨hBS, hw⟩, hblock, htail, hcross⟩
    refine ⟨hBS, hw, hblock, htail, ?_⟩
    intro x hx y hy
    exact hcross y ((mem_blockWord_iff B T hT y).mpr hy) x ((hw.2 x).mpr hx)
  · rintro ⟨hBS, hw, hblock, htail, hcross⟩
    refine ⟨⟨hBS, hw⟩, hblock, htail, ?_⟩
    intro y hy x hx
    exact hcross x ((hw.2 x).mp hx) y ((mem_blockWord_iff B T hT y).mp hy)

/-- Signed first-block cancellation with the literal remaining word still visible. -/
theorem signed_blockContinuation
    (R : V → V → Prop) (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (S B : Finset V) (r : V) (hr : r ∈ B) (hmax : ∀ v ∈ B, v ≤ r) (w : List V) :
    (∑ T ∈ (B.erase r).powerset, (-1 : ℤ) ^ T.card *
      if fullOn S (blockWord B T ++ w) ∧ wordCompatible R (blockWord B T ++ w)
        then 1 else 0) =
      (if B ⊆ S ∧ fullOn (S \ B) w ∧ wordCompatible R w ∧
        (∀ x ∈ S \ B, ∀ y ∈ B, ¬ R x y) ∧
        (∀ v ∈ B, sinkOn R B v ↔ v = r) then 1 else 0) := by
  let rest : Prop := B ⊆ S ∧ fullOn (S \ B) w ∧ wordCompatible R w ∧
    ∀ x ∈ S \ B, ∀ y ∈ B, ¬ R x y
  have hsplit : ∀ T ∈ (B.erase r).powerset,
      (fullOn S (blockWord B T ++ w) ∧ wordCompatible R (blockWord B T ++ w)) ↔
        rest ∧ wordCompatible R (blockWord B T) := by
    intro T hT
    rw [fullOn_compatible_blockWord_append_iff R S B T
      ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _))]
    dsimp [rest]
    grind
  rw [Finset.sum_congr rfl (g := fun T => (-1 : ℤ) ^ T.card *
    if rest ∧ wordCompatible R (blockWord B T) then 1 else 0)
    (fun T hT => by simp only [hsplit T hT])]
  by_cases hrest : rest
  · simp only [hrest, true_and, blockCancellation_uniqueSink R hinc B r hr hmax]
    dsimp [rest] at hrest
    split_ifs <;> grind
  · simp only [hrest, false_and, ite_false, mul_zero, Finset.sum_const_zero]
    dsimp [rest] at hrest
    split_ifs <;> grind

/-- Scalar extension of the literal signed cancellation. -/
theorem signed_blockContinuation_scalar {K : Type*} [CommRing K]
    (R : V → V → Prop) (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (S B : Finset V) (r : V) (hr : r ∈ B) (hmax : ∀ v ∈ B, v ≤ r) (w : List V) :
    (∑ T ∈ (B.erase r).powerset, (-1 : K) ^ T.card *
      if fullOn S (blockWord B T ++ w) ∧ wordCompatible R (blockWord B T ++ w)
        then 1 else 0) =
      (if B ⊆ S ∧ fullOn (S \ B) w ∧ wordCompatible R w ∧
        (∀ x ∈ S \ B, ∀ y ∈ B, ¬ R x y) ∧
        (∀ v ∈ B, sinkOn R B v ↔ v = r) then 1 else 0) := by
  have h := congrArg (Int.castRingHom K)
    (signed_blockContinuation R hinc S B r hr hmax w)
  simpa only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, apply_ite] using h

end

end VerticalStripLLT.Components

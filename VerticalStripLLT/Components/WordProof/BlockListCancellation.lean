import VerticalStripLLT.Components.WordProof.BlockCancellation
import VerticalStripLLT.Components.WordProof.BlockWordSupport
import Mathlib.Tactic.Ring

/-! Iterated signed cancellation for a list of rooted mountain blocks. -/

namespace VerticalStripLLT.Components

open Classical
open scoped BigOperators

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- The signed contribution of one rooted block, before the sink test is simplified. -/
def rootedBlockSum (R : V → V → Prop) (B : Finset V) (r : V) : ℤ :=
  ∑ T ∈ (B.erase r).powerset,
    (-1 : ℤ) ^ T.card *
      (if wordCompatible R (blockWord B T) then 1 else 0)

/-- The iterated local signed sum over a list of rooted blocks. -/
def rootedBlockListSum (R : V → V → Prop) :
    List (Finset V × V) → ℤ
  | [] => 1
  | (B, r) :: blocks =>
      rootedBlockSum R B r * rootedBlockListSum R blocks

/-- A tail-choice sum, with the continuation evaluated after all blocks have
been assigned tails.  Keeping the choices as a list avoids a dependent finite
product indexed by the blocks. -/
def signedTailSum (R : V → V → Prop) :
    List (Finset V × V) → (List (Finset V) → ℤ) → ℤ
  | [], value => value []
  | (B, r) :: blocks, value =>
      ∑ T ∈ (B.erase r).powerset,
        (-1 : ℤ) ^ T.card *
          signedTailSum R blocks (fun tails => value (T :: tails))

theorem signedTailSum_congr (R : V → V → Prop)
    (blocks : List (Finset V × V)) {f g : List (Finset V) → ℤ}
    (hfg : ∀ tails, f tails = g tails) :
    signedTailSum R blocks f = signedTailSum R blocks g := by
  exact congrArg (signedTailSum R blocks) (funext hfg)

theorem signedTailSum_smul (R : V → V → Prop)
    (blocks : List (Finset V × V)) (c : ℤ) (f : List (Finset V) → ℤ) :
    signedTailSum R blocks (fun tails => c * f tails) =
      c * signedTailSum R blocks f := by
  induction blocks generalizing f with
  | nil => rfl
  | cons Br blocks ih =>
      simp only [signedTailSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [ih]
      ring

theorem signedTailSum_cons_factor (R : V → V → Prop)
    (B : Finset V) (r : V) (blocks : List (Finset V × V))
    (f g : List (Finset V) → ℤ) (k : Finset V → ℤ)
    (hfactor : ∀ T ∈ (B.erase r).powerset, ∀ tails,
      f (T :: tails) = k T * g tails) :
    signedTailSum R ((B, r) :: blocks) f =
      (∑ T ∈ (B.erase r).powerset, (-1 : ℤ) ^ T.card * k T) *
        signedTailSum R blocks g := by
  rw [signedTailSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [signedTailSum_congr R blocks (hfactor T hT), signedTailSum_smul, mul_assoc]

/-- The flattened compatibility indicator on a complete tail list.  Invalid
tail lists contribute zero, which makes pointwise factorization hypotheses
usable without a dependent list type. -/
def flattenedTailCompatibilityIndicator (R : V → V → Prop)
    (blocks : List (Finset V × V)) (tails : List (Finset V)) : ℤ :=
  if _h : tails.length = blocks.length ∧
      ∀ BT ∈ blocks.zip tails, BT.2 ⊆ BT.1.1 then
    if wordCompatible R
        ((blocks.zip tails).map (fun BT => blockWord BT.1.1 BT.2)).flatten then 1 else 0
  else 0

def flattenedTailCompatibilitySum (R : V → V → Prop)
    (blocks : List (Finset V × V)) : ℤ :=
  signedTailSum R blocks (flattenedTailCompatibilityIndicator R blocks)

theorem flattenedTailCompatibilitySum_eq_rootedBlockListSum_of_factor
    (R : V → V → Prop) (blocks : List (Finset V × V))
    (hcross : blocks.Pairwise
      (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u))
    (hfactor : ∀ B r blocks',
      ((B, r) :: blocks').Pairwise
        (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u) →
      ∀ T ∈ (B.erase r).powerset, ∀ tails,
      flattenedTailCompatibilityIndicator R ((B, r) :: blocks') (T :: tails) =
        (if wordCompatible R (blockWord B T) then 1 else 0) *
          flattenedTailCompatibilityIndicator R blocks' tails) :
    flattenedTailCompatibilitySum R blocks = rootedBlockListSum R blocks := by
  induction blocks with
  | nil => simp [flattenedTailCompatibilitySum, signedTailSum, rootedBlockListSum,
      flattenedTailCompatibilityIndicator, wordCompatible]
  | cons Br blocks ih =>
      obtain ⟨B, r⟩ := Br
      have hcross_head := (List.pairwise_cons.mp hcross)
      rw [flattenedTailCompatibilitySum, signedTailSum_cons_factor R B r blocks
        (flattenedTailCompatibilityIndicator R ((B, r) :: blocks))
        (flattenedTailCompatibilityIndicator R blocks)
        (fun T => if wordCompatible R (blockWord B T) then 1 else 0)]
      · change rootedBlockSum R B r * flattenedTailCompatibilitySum R blocks = _
        rw [ih hcross_head.2]
        rfl
      · intro T hT tails
        exact hfactor B r blocks hcross T hT tails

theorem rootedBlockSum_eq_uniqueSink (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) (r : V)
    (hr : r ∈ B) (hmax : ∀ u ∈ B, u ≤ r) :
    rootedBlockSum R B r =
      if (∀ u ∈ B, sinkOn R B u ↔ u = r) then 1 else 0 := by
  exact blockCancellation_uniqueSink R hinc B r hr hmax

/-- Iterated local cancellation detects exactly the rooted unique-sink condition. -/
theorem rootedBlockListSum_eq_uniqueSinks (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (blocks : List (Finset V × V))
    (hroot : ∀ Br ∈ blocks, Br.2 ∈ Br.1 ∧ ∀ u ∈ Br.1, u ≤ Br.2) :
    rootedBlockListSum R blocks =
      if ∀ Br ∈ blocks, ∀ u ∈ Br.1, sinkOn R Br.1 u ↔ u = Br.2 then 1 else 0 := by
  induction blocks with
  | nil => simp [rootedBlockListSum]
  | cons Br blocks ih =>
      obtain ⟨hr, hmax⟩ := hroot Br (by simp)
      have hroot_tail : ∀ B ∈ blocks, B.2 ∈ B.1 ∧ ∀ u ∈ B.1, u ≤ B.2 := by
        intro B hB
        exact hroot B (by simp [hB])
      rw [rootedBlockListSum, rootedBlockSum_eq_uniqueSink R hinc Br.1 Br.2 hr hmax,
        ih hroot_tail]
      simp only [List.forall_mem_cons]
      split_ifs <;> grind

theorem flattenedTailCompatibilitySum_eq_of_cross_factor
    (R : V → V → Prop) (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (blocks : List (Finset V × V))
    (hroot : ∀ Br ∈ blocks, Br.2 ∈ Br.1 ∧ ∀ u ∈ Br.1, u ≤ Br.2)
    (hcross : blocks.Pairwise
      (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u))
    (hfactor : ∀ B r blocks',
      ((B, r) :: blocks').Pairwise
        (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u) →
      ∀ T ∈ (B.erase r).powerset, ∀ tails,
      flattenedTailCompatibilityIndicator R ((B, r) :: blocks') (T :: tails) =
        (if wordCompatible R (blockWord B T) then 1 else 0) *
          flattenedTailCompatibilityIndicator R blocks' tails) :
    flattenedTailCompatibilitySum R blocks =
      if (∀ Br ∈ blocks, ∀ u ∈ Br.1, sinkOn R Br.1 u ↔ u = Br.2) ∧
        blocks.Pairwise (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u) then 1
      else 0 := by
  rw [flattenedTailCompatibilitySum_eq_rootedBlockListSum_of_factor R blocks hcross hfactor,
    rootedBlockListSum_eq_uniqueSinks R hinc blocks hroot]
  simp [hcross]

/-- Under the cross-block condition, flattened compatibility is just the conjunction
of the internal block compatibilities.  This is the pointwise bridge used when
reindexing the iterated tail sum. -/
theorem blockWords_flatten_indicator_eq_of_cross
    (R : V → V → Prop) (blocks : List (Finset V × Finset V))
    (hsub : ∀ BT ∈ blocks, BT.2 ⊆ BT.1)
    (hcross : blocks.Pairwise
      (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u)) :
    (if wordCompatible R
        ((blocks.map (fun BT => blockWord BT.1 BT.2)).flatten) then (1 : ℤ) else 0) =
      if ∀ BT ∈ blocks, wordCompatible R (blockWord BT.1 BT.2) then 1 else 0 := by
  rw [wordCompatible_blockWords_flatten_iff R blocks hsub]
  simp [hcross]

/-- The cross-block bridge in the cons form needed by the recursive tail sum. -/
theorem blockWords_flatten_indicator_cons_eq
    (R : V → V → Prop) (head : Finset V × Finset V)
    (tail : List (Finset V × Finset V))
    (hsub_head : head.2 ⊆ head.1)
    (hsub_tail : ∀ BT ∈ tail, BT.2 ⊆ BT.1)
    (hcross : (head :: tail).Pairwise
      (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u)) :
    (if wordCompatible R
        (((head :: tail).map (fun BT => blockWord BT.1 BT.2)).flatten) then (1 : ℤ) else 0) =
      (if wordCompatible R (blockWord head.1 head.2) then 1 else 0) *
        (if wordCompatible R
            ((tail.map (fun BT => blockWord BT.1 BT.2)).flatten) then 1 else 0) := by
  have hsub : ∀ BT ∈ head :: tail, BT.2 ⊆ BT.1 := by
    intro BT hBT
    rcases List.mem_cons.mp hBT with rfl | hBT
    · exact hsub_head
    · exact hsub_tail BT hBT
  have htail_cross := (List.pairwise_cons.mp hcross).2
  have hhead_compat :
      wordCompatible R (blockWord head.1 head.2) ↔
        ∀ BT ∈ [head], wordCompatible R (blockWord BT.1 BT.2) := by
    simp
  have htail_compat := wordCompatible_blockWords_flatten_iff R tail hsub_tail
  have hfull := wordCompatible_blockWords_flatten_iff R (head :: tail) hsub
  rw [hfull, htail_compat]
  simp only [hcross, htail_cross, and_true, List.forall_mem_cons]
  split_ifs <;> simp_all

end

end VerticalStripLLT.Components

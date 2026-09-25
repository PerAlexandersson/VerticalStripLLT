import VerticalStripLLT.Concat
import VerticalStripLLT.PathBounds
import VerticalStripLLT.Coloring
import Mathlib.Tactic.Ring

/-! Multiplicativity of the coloring LLT under concatenation.

The candidate originated from Aristotle; see `docs/ARISTOTLE.md` for provenance.
We identify the two graph components before factoring weights and finite sums.
-/

open scoped BigOperators

namespace VerticalStripLLT

namespace SchroderPath

/-- Scanner facts for the left block of a concatenation. -/
theorem normalFrom_concat_left {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hi : i < n) :
    Step.normalFrom 0 0 i j (P.steps ++ Q.steps) = Step.normalFrom 0 0 i j P.steps := by
  rw [Step.normalFrom_append_of_valid n 0 0 i j P.steps Q.steps P.valid]
  cases h : Step.normalFrom n n i j Q.steps
  · simp
  · have := Step.normalFrom_lower_bound n n i j h
    lia

theorem strictFrom_concat_left {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hi : i < n) :
    Step.strictFrom 0 0 i j (P.steps ++ Q.steps) = Step.strictFrom 0 0 i j P.steps := by
  rw [Step.strictFrom_append_of_valid n 0 0 i j P.steps Q.steps P.valid]
  cases h : Step.strictFrom n n i j Q.steps
  · simp
  · have := Step.strictFrom_lower_bound n n i j h
    lia

theorem normalFrom_concat_right {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) :
    Step.normalFrom 0 0 (n + i) (n + j) (P.steps ++ Q.steps) =
      Step.normalFrom 0 0 i j Q.steps := by
  rw [Step.normalFrom_append_of_valid n 0 0 _ _ P.steps Q.steps P.valid]
  have hP : Step.normalFrom 0 0 (n + i) (n + j) P.steps = false := by
    cases h : Step.normalFrom 0 0 (n + i) (n + j) P.steps
    · rfl
    · have := Step.normalFrom_upper_bound n 0 0 _ _ P.valid h
      lia
  have hQ := Step.normalFrom_translate 0 0 i j n Q.steps
  simp only [Nat.zero_add] at hQ
  rw [hP, Bool.false_or, Nat.add_comm n i, Nat.add_comm n j, hQ]

theorem strictFrom_concat_right {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) :
    Step.strictFrom 0 0 (n + i) (n + j) (P.steps ++ Q.steps) =
      Step.strictFrom 0 0 i j Q.steps := by
  rw [Step.strictFrom_append_of_valid n 0 0 _ _ P.steps Q.steps P.valid]
  have hP : Step.strictFrom 0 0 (n + i) (n + j) P.steps = false := by
    cases h : Step.strictFrom 0 0 (n + i) (n + j) P.steps
    · rfl
    · have := Step.strictFrom_upper_bound n 0 0 _ _ P.valid h
      lia
  have hQ := Step.strictFrom_translate 0 0 i j n Q.steps
  simp only [Nat.zero_add] at hQ
  rw [hP, Bool.false_or, Nat.add_comm n i, Nat.add_comm n j, hQ]

theorem normalFrom_concat_mixed_lr {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hi : i < n) :
    Step.normalFrom 0 0 i (n + j) (P.steps ++ Q.steps) = false := by
  rw [normalFrom_concat_left P Q i _ hi]
  cases h : Step.normalFrom 0 0 i (n + j) P.steps
  · rfl
  · have := Step.normalFrom_upper_bound n 0 0 _ _ P.valid h
    lia

theorem strictFrom_concat_mixed_lr {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hi : i < n) :
    Step.strictFrom 0 0 i (n + j) (P.steps ++ Q.steps) = false := by
  rw [strictFrom_concat_left P Q i _ hi]
  cases h : Step.strictFrom 0 0 i (n + j) P.steps
  · rfl
  · have := Step.strictFrom_upper_bound n 0 0 _ _ P.valid h
    lia

theorem normalFrom_concat_mixed_rl {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hj : j < n) :
    Step.normalFrom 0 0 (n + i) j (P.steps ++ Q.steps) = false := by
  cases h : Step.normalFrom 0 0 (n + i) j (P.steps ++ Q.steps)
  · rfl
  · have := Step.normalFrom_lt 0 0 _ _ h
    lia

theorem strictFrom_concat_mixed_rl {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (i j : ℕ) (hj : j < n) :
    Step.strictFrom 0 0 (n + i) j (P.steps ++ Q.steps) = false := by
  cases h : Step.strictFrom 0 0 (n + i) j (P.steps ++ Q.steps)
  · rfl
  · have := Step.strictFrom_lt_of_valid (n + k) 0 0 _ _ (P.concat Q).valid h
    lia

/-- Embedding of the left block's vertex pairs into the concatenation. -/
def leftPairEmb (n k : ℕ) : Fin n × Fin n ↪ Fin (n + k) × Fin (n + k) :=
  ⟨fun p => (Fin.castAdd k p.1, Fin.castAdd k p.2), fun p q h => by
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    exact Prod.ext h.1 h.2⟩

/-- Embedding of the right block's vertex pairs (shifted by `n`) into the concatenation. -/
def rightPairEmb (n k : ℕ) : Fin k × Fin k ↪ Fin (n + k) × Fin (n + k) :=
  ⟨fun p => (Fin.natAdd n p.1, Fin.natAdd n p.2), fun p q h => by
    simp only [Prod.mk.injEq, Fin.natAdd_inj] at h
    exact Prod.ext h.1 h.2⟩

@[simp] theorem leftPairEmb_apply {n k : ℕ} (p : Fin n × Fin n) :
    leftPairEmb n k p = (Fin.castAdd k p.1, Fin.castAdd k p.2) := rfl

@[simp] theorem rightPairEmb_apply {n k : ℕ} (p : Fin k × Fin k) :
    rightPairEmb n k p = (Fin.natAdd n p.1, Fin.natAdd n p.2) := rfl

theorem disjoint_left_right_maps {n k : ℕ} (A : Finset (Fin n × Fin n))
    (B : Finset (Fin k × Fin k)) :
    Disjoint (A.map (leftPairEmb n k)) (B.map (rightPairEmb n k)) := by
  refine Finset.disjoint_left.2 ?_
  intro e ha hb
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
  obtain ⟨b, -, hb⟩ := Finset.mem_map.1 hb
  have h := congrArg (fun p => p.1.val) hb
  simp only [leftPairEmb_apply, rightPairEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at h
  have := a.1.isLt
  lia

theorem not_mem_left_map {n k : ℕ} {A : Finset (Fin n × Fin n)}
    {e : Fin (n + k) × Fin (n + k)} (h : n ≤ e.1.val ∨ n ≤ e.2.val) :
    e ∉ A.map (leftPairEmb n k) := by
  intro he
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 he
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  simp only [leftPairEmb_apply, Fin.val_castAdd] at h
  lia

theorem not_mem_right_map {n k : ℕ} {B : Finset (Fin k × Fin k)}
    {e : Fin (n + k) × Fin (n + k)} (h : e.1.val < n ∨ e.2.val < n) :
    e ∉ B.map (rightPairEmb n k) := by
  intro he
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 he
  simp only [rightPairEmb_apply, Fin.val_natAdd] at h
  lia

theorem mem_left_map_iff {n k : ℕ} {A : Finset (Fin n × Fin n)} (i j : Fin n) :
    (Fin.castAdd k i, Fin.castAdd k j) ∈ A.map (leftPairEmb n k) ↔ (i, j) ∈ A :=
  Finset.mem_map' (leftPairEmb n k) (a := (i, j))

theorem mem_right_map_iff {n k : ℕ} {B : Finset (Fin k × Fin k)} (i j : Fin k) :
    (Fin.natAdd n i, Fin.natAdd n j) ∈ B.map (rightPairEmb n k) ↔ (i, j) ∈ B :=
  Finset.mem_map' (rightPairEmb n k) (a := (i, j))

theorem concat_normalEdges {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k) :
    (P.concat Q).normalEdges =
      P.normalEdges.map (leftPairEmb n k) ∪ Q.normalEdges.map (rightPairEmb n k) := by
  ext ⟨a, b⟩
  rw [Finset.mem_union]
  change ((a, b) ∈ Finset.univ.filter (fun e =>
    Step.normalFrom 0 0 e.1.val e.2.val (P.steps ++ Q.steps))) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [mem_left_map_iff, iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [normalEdges, normalFrom_concat_left P Q _ _ i.isLt]
    | right j =>
      rw [iff_false_intro (not_mem_left_map (by simp)),
        iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [normalFrom_concat_mixed_lr P Q _ _ i.isLt]
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [iff_false_intro (not_mem_left_map (by simp)),
        iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [normalFrom_concat_mixed_rl P Q _ _ j.isLt]
    | right j =>
      rw [mem_right_map_iff, iff_false_intro (not_mem_left_map (by simp)), false_or]
      simp [normalEdges, normalFrom_concat_right P Q]

theorem concat_strictEdges {n k : ℕ} (P : SchroderPath n) (Q : SchroderPath k) :
    (P.concat Q).strictEdges =
      P.strictEdges.map (leftPairEmb n k) ∪ Q.strictEdges.map (rightPairEmb n k) := by
  ext ⟨a, b⟩
  rw [Finset.mem_union]
  change ((a, b) ∈ Finset.univ.filter (fun e =>
    Step.strictFrom 0 0 e.1.val e.2.val (P.steps ++ Q.steps))) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [mem_left_map_iff, iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [strictEdges, strictFrom_concat_left P Q _ _ i.isLt]
    | right j =>
      rw [iff_false_intro (not_mem_left_map (by simp)),
        iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [strictFrom_concat_mixed_lr P Q _ _ i.isLt]
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [iff_false_intro (not_mem_left_map (by simp)),
        iff_false_intro (not_mem_right_map (by simp)), or_false]
      simp [strictFrom_concat_mixed_rl P Q _ _ j.isLt]
    | right j =>
      rw [mem_right_map_iff, iff_false_intro (not_mem_left_map (by simp)), false_or]
      simp [strictEdges, strictFrom_concat_right P Q]

end SchroderPath

open SchroderPath in
theorem admissible_concat_append {n k m : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (c₁ : Fin n → Fin m) (c₂ : Fin k → Fin m) :
    admissible (P.concat Q) (Fin.append c₁ c₂) ↔ admissible P c₁ ∧ admissible Q c₂ := by
  simp only [admissible, concat_strictEdges, Finset.mem_union, or_imp, forall_and,
    Finset.forall_mem_map]
  simp only [leftPairEmb_apply, rightPairEmb_apply, Fin.append_left, Fin.append_right]

open SchroderPath in
theorem ascentCount_concat_append {n k m : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (c₁ : Fin n → Fin m) (c₂ : Fin k → Fin m) :
    ascentCount (P.concat Q) (Fin.append c₁ c₂) = ascentCount P c₁ + ascentCount Q c₂ := by
  unfold ascentCount
  rw [concat_normalEdges, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (disjoint_left_right_maps _ _)),
    Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
  congr 2 <;> ext e <;>
    simp [Finset.mem_filter, Function.comp_apply, leftPairEmb_apply,
      rightPairEmb_apply, Fin.append_left, Fin.append_right]

theorem coloringWeight_concat_append {n k m : ℕ} (P : SchroderPath n) (Q : SchroderPath k)
    (c₁ : Fin n → Fin m) (c₂ : Fin k → Fin m) :
    coloringWeight (P.concat Q) (Fin.append c₁ c₂) =
      coloringWeight P c₁ * coloringWeight Q c₂ := by
  classical
  unfold coloringWeight
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, admissible_concat_append,
    ascentCount_concat_append]
  by_cases h₁ : admissible P c₁ <;> by_cases h₂ : admissible Q c₂ <;>
    simp only [h₁, h₂, and_self, and_true, and_false, ite_true,
      ite_false, zero_mul, mul_zero]
  rw [pow_add, MvPolynomial.C_mul]
  ring

theorem coloringLLT_concat {n k : ℕ} (P : SchroderPath n)
    (Q : SchroderPath k) (m : ℕ) :
    coloringLLT (P.concat Q) m = coloringLLT P m * coloringLLT Q m := by
  unfold coloringLLT
  rw [Fintype.sum_mul_sum, ← Fintype.sum_prod_type',
    ← Fintype.sum_equiv (Fin.appendEquiv n k) (fun p => coloringWeight (P.concat Q)
      (Fin.append p.1 p.2)) _ (fun _ => rfl)]
  exact Fintype.sum_congr _ _ fun p => coloringWeight_concat_append P Q p.1 p.2

end VerticalStripLLT

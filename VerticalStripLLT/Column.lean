import VerticalStripLLT.Coloring

/-! The one-column Schröder paths.

The path `n d^k e` has `k` strict edges, namely the adjacent pairs of its
`k + 1` vertices.  We record this as a useful finite base family for later
coloring arguments.
-/

namespace VerticalStripLLT

open Step

namespace SchroderPath

private theorem valid_diag_e (k x : ℕ) :
    Step.validFrom (x + k + 1) x (x + 1)
        (List.replicate k diagonal ++ [east]) = true := by
  induction k generalizing x with
  | zero => simp [Step.validFrom]
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, Step.validFrom]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x + 1)

private theorem strict_diag_e (k x u v : ℕ) :
    Step.strictFrom x (x + 1) u v
        (List.replicate k diagonal ++ [east]) = true ↔
      x ≤ u ∧ u < x + k ∧ u + 1 = v := by
  induction k generalizing x with
  | zero => simp [Step.strictFrom]; lia
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, Step.strictFrom,
        Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      rw [ih]
      constructor <;> intro h
      · rcases h with h | h
        · rcases h with ⟨hu, hv⟩
          exact ⟨by lia, by lia, by lia⟩
        · rcases h with ⟨hu, huk, huv⟩
          exact ⟨by lia, by lia, huv⟩
      · by_cases hu : u = x
        · left
          exact ⟨hu, by lia⟩
        · right
          rcases h with ⟨hxu, huk, huv⟩
          exact ⟨by lia, by lia, huv⟩

private theorem normal_diag_e (k x u v : ℕ) :
    Step.normalFrom x (x + 1) u v
        (List.replicate k diagonal ++ [east]) = false := by
  induction k generalizing x with
  | zero => simp [Step.normalFrom]; lia
  | succ k ih =>
      simp [List.replicate_succ, Step.normalFrom, ih]
      lia

/-- The vertical-strip column path `n d^k e`. -/
def column (k : ℕ) : SchroderPath (k + 1) :=
  ⟨north :: List.replicate k diagonal ++ [east], by
    simpa [Step.validFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (valid_diag_e k 0)⟩

theorem column_normalEdges (k : ℕ) : (column k).normalEdges = ∅ := by
  ext e
  simp [normalEdges, column, Step.normalFrom, normal_diag_e]

theorem column_strict_mem_iff (k : ℕ) (e : Fin (k + 1) × Fin (k + 1)) :
    e ∈ (column k).strictEdges ↔ e.1.val + 1 = e.2.val := by
  simp only [strictEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  change Step.strictFrom 0 1 e.1.val e.2.val
      (List.replicate k diagonal ++ [east]) = true ↔ _
  rw [strict_diag_e]
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    refine ⟨Nat.zero_le _, ?_, h⟩
    have hv := e.2.isLt
    lia

theorem column_strictEdges (k : ℕ) :
    (column k).strictEdges =
      Finset.univ.filter (fun e : Fin (k + 1) × Fin (k + 1) =>
        e.1.val + 1 = e.2.val) := by
  ext e
  simpa using column_strict_mem_iff k e

theorem column_ascentCount {m k : ℕ} (c : Fin (k + 1) → Fin m) :
    ascentCount (column k) c = 0 := by
  simp [ascentCount, column_normalEdges]

theorem admissible_column_iff {m k : ℕ} (c : Fin (k + 1) → Fin m) :
    admissible (column k) c ↔ StrictMono c := by
  constructor
  · intro h
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    apply h (i.castSucc, i.succ)
    rw [column_strict_mem_iff]
    simp
  · intro h e he
    have hev : e.1.val + 1 = e.2.val :=
      (column_strict_mem_iff k e).mp he
    apply h
    change e.1.val < e.2.val
    lia

end SchroderPath
end VerticalStripLLT

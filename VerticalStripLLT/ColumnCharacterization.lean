import VerticalStripLLT.WordCounts
import VerticalStripLLT.Column

namespace VerticalStripLLT

namespace Step

private theorem valid_equal_zero_counts (n x : ℕ) {w : List Step}
    (hv : validFrom n x x w = true)
    (hn : northCount w = 0) (he : eastCount w = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons s w =>
      cases s with
      | north => simp [northCount] at hn
      | diagonal =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          lia
      | east =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          lia

private theorem valid_gap_one_one_east (n x : ℕ) {w : List Step}
    (hv : validFrom n x (x + 1) w = true)
    (hn : northCount w = 0) (he : eastCount w = 1) :
    ∃ k : ℕ, w = List.replicate k diagonal ++ [east] := by
  cases w with
  | nil => simp [eastCount] at he
  | cons s w =>
      cases s with
      | north => simp [northCount] at hn
      | diagonal =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          have hn' : northCount w = 0 := by simpa [northCount] using hn
          have he' : eastCount w = 1 := by simpa [eastCount] using he
          obtain ⟨k, hk⟩ := valid_gap_one_one_east n (x + 1) hv.2 hn' he'
          refine ⟨k + 1, ?_⟩
          simp [List.replicate_succ, hk, List.cons_append]
      | east =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          have hn' : northCount w = 0 := by simpa [northCount] using hn
          have he' : eastCount w = 0 := by simpa [eastCount] using he
          have hw : w = [] := valid_equal_zero_counts n (x + 1) hv.2 hn' he'
          exact ⟨0, by simp [hw]⟩

theorem valid_one_east_column {n : ℕ} (P : SchroderPath n)
    (he : Step.eastCount P.steps = 1) :
    ∃ k : ℕ, P.steps = Step.north :: List.replicate k Step.diagonal ++ [Step.east] := by
  have hn : Step.northCount P.steps = 1 :=
    P.northCount_eq_eastCount.trans he
  cases hsteps : P.steps with
  | nil => simp [hsteps, Step.eastCount] at he
  | cons s w =>
      cases s with
      | north =>
          have hv : Step.validFrom n 0 1 w = true := by
            simpa [hsteps, Step.validFrom] using P.valid
          have hn' : Step.northCount w = 0 := by
            simpa [hsteps, Step.northCount] using hn
          have he' : Step.eastCount w = 1 := by
            simpa [hsteps, Step.eastCount] using he
          obtain ⟨k, hk⟩ := Step.valid_gap_one_one_east n 0 hv hn' he'
          exact ⟨k, by simp [hk]⟩
      | diagonal =>
          have hv := P.valid
          simp [hsteps, Step.validFrom] at hv
      | east =>
          have hv := P.valid
          simp [hsteps, Step.validFrom] at hv

theorem valid_one_east_column_size {n : ℕ} (P : SchroderPath n)
    (he : Step.eastCount P.steps = 1) :
    ∃ k : ℕ, P.steps = Step.north :: List.replicate k Step.diagonal ++ [Step.east] ∧ n = k + 1 := by
  obtain ⟨k, hk⟩ := valid_one_east_column P he
  refine ⟨k, hk, ?_⟩
  have hv := Step.validFrom_endpoint n 0 0 P.steps P.valid
  rw [hk, Step.endpointFrom_counts] at hv
  have hx := congrArg Prod.fst hv
  simp [Step.eastCount, Step.diagonalCount, List.count_replicate] at hx
  lia

end Step
end VerticalStripLLT

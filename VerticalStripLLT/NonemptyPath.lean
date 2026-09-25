import VerticalStripLLT.WordCounts

namespace VerticalStripLLT

namespace SchroderPath

private theorem valid_zero_empty {P : SchroderPath 0} : P.steps = [] := by
  cases hsteps : P.steps with
  | nil => rfl
  | cons s w =>
      cases s with
      | north =>
          have hv := P.valid
          simp only [hsteps, Step.validFrom] at hv
          have hb := Step.validFrom_bounds 0 0 1 hv
          lia
      | diagonal =>
          have hv := P.valid
          simp [hsteps, Step.validFrom] at hv
      | east =>
          have hv := P.valid
          simp [hsteps, Step.validFrom] at hv

theorem steps_eq_nil_iff {n : ℕ} (P : SchroderPath n) :
    P.steps = [] ↔ n = 0 := by
  constructor
  · intro hs
    have hv := P.valid
    rw [hs] at hv
    simp only [Step.validFrom, Bool.and_eq_true, beq_iff_eq] at hv
    exact hv.1.symm
  · intro hn
    subst n
    exact valid_zero_empty (P := P)

theorem east_mem_of_pos {n : ℕ} (P : SchroderPath n) (hn : 0 < n) :
    Step.east ∈ P.steps := by
  by_contra he
  have hec : Step.eastCount P.steps = 0 := by
    simpa only [Step.eastCount] using List.count_eq_zero_of_not_mem he
  have hnc : Step.northCount P.steps = 0 := by
    rw [P.northCount_eq_eastCount, hec]
  cases hsteps : P.steps with
  | nil =>
      have : n = 0 := (steps_eq_nil_iff P).mp hsteps
      lia
  | cons s w =>
      cases s with
      | north =>
          simp [hsteps, Step.northCount] at hnc
      | diagonal =>
          have hv := P.valid
          simp [hsteps, Step.validFrom] at hv
      | east =>
          exact he (by simp [hsteps])

end SchroderPath
end VerticalStripLLT

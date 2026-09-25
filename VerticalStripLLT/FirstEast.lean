import VerticalStripLLT.WordCounts

namespace VerticalStripLLT

namespace Step

def firstEastHeightFrom (y : ℕ) : List Step → ℕ
  | [] => 0
  | north :: w => firstEastHeightFrom (y + 1) w
  | diagonal :: w => firstEastHeightFrom (y + 1) w
  | east :: _ => y

def firstEastHeight (w : List Step) : ℕ := firstEastHeightFrom 0 w

theorem firstEastHeightFrom_append_east (y : ℕ) (U W : List Step)
    (he : east ∉ U) :
    firstEastHeightFrom y (U ++ east :: W) =
      y + northCount U + diagonalCount U := by
  induction U generalizing y with
  | nil => simp [firstEastHeightFrom, northCount, diagonalCount]
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, firstEastHeightFrom]
          rw [ih (y := y + 1) (by simpa using he)]
          simp [northCount, diagonalCount, Nat.add_comm, Nat.add_left_comm]
      | diagonal =>
          simp only [List.cons_append, firstEastHeightFrom]
          rw [ih (y := y + 1) (by simpa using he)]
          simp [northCount, diagonalCount, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]
      | east => simp at he

theorem exists_east_decomposition {w : List Step} (he : east ∈ w) :
    ∃ U W, w = U ++ east :: W ∧ east ∉ U := by
  induction w with
  | nil => simp at he
  | cons s w ih =>
      cases s with
      | east => exact ⟨[], w, rfl, by simp⟩
      | north =>
          rcases ih (by simpa using he) with ⟨U, W, hw, hU⟩
          exact ⟨north :: U, W, by simp [hw], by simpa using hU⟩
      | diagonal =>
          rcases ih (by simpa using he) with ⟨U, W, hw, hU⟩
          exact ⟨diagonal :: U, W, by simp [hw], by simpa using hU⟩

theorem firstEastHeight_eq_counts {w : List Step} (he : east ∈ w) :
    ∃ U W, w = U ++ east :: W ∧ east ∉ U ∧
      firstEastHeight w = northCount U + diagonalCount U := by
  rcases exists_east_decomposition he with ⟨U, W, hw, hU⟩
  refine ⟨U, W, hw, hU, ?_⟩
  subst w
  simpa [firstEastHeight] using firstEastHeightFrom_append_east 0 U W hU

theorem firstEastHeight_append_east (U W : List Step) (he : east ∉ U) :
    firstEastHeight (U ++ east :: W) = (endpointFrom 0 0 U).2 := by
  unfold firstEastHeight
  rw [firstEastHeightFrom_append_east 0 U W he]
  rw [endpointFrom_counts]

end Step
end VerticalStripLLT

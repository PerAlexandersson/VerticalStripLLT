import VerticalStripLLT.BounceSeed

namespace VerticalStripLLT

open Step

namespace Step

theorem endpointFrom_noEast (x y : ℕ) (w : List Step) (hw : east ∉ w) :
    endpointFrom x y w = (x + diagonalCount w, y + w.length) := by
  induction w generalizing x y with
  | nil => simp [endpointFrom, diagonalCount]
  | cons s w ih =>
      cases s with
      | north =>
          simp only [endpointFrom, List.length_cons]
          rw [ih (x := x) (y := y + 1) (by simpa using hw)]
          simp [diagonalCount, Nat.add_comm, Nat.add_left_comm]
      | diagonal =>
          simp only [endpointFrom, List.length_cons]
          rw [ih (x := x + 1) (y := y + 1) (by simpa using hw)]
          simp [diagonalCount, Nat.add_comm, Nat.add_left_comm]
      | east => simp at hw

end Step

namespace BounceSeed

theorem singleBounce_coordinates (U V : List Step) (s t : Step)
    (h : BounceSeed (U ++ s :: t :: (V ++ [diagonal])))
    (hindex : U.length + 1 = diagonalCount
      (U ++ s :: t :: (V ++ [diagonal]))) :
    (endpointFrom 0 0 U).2 =
        (endpointFrom 0 0 (U ++ s :: t :: V)).1 ∧
      (endpointFrom 0 0 (U ++ s :: t :: V)).1 + 1 <
        (endpointFrom 0 0 (U ++ s :: t :: V)).2 := by
  let R := U ++ s :: t :: V
  have hword : U ++ s :: t :: (V ++ [diagonal]) = R ++ [diagonal] := by
    simp [R, List.append_assoc]
  have hR : east ∉ R := by
    intro he
    apply h.noEast
    rw [hword]
    exact List.mem_append_left _ he
  have hU : east ∉ U := by
    intro he
    apply hR
    simp [R, he]
  have hcount : diagonalCount (U ++ s :: t :: (V ++ [diagonal])) =
      diagonalCount R + 1 := by
    rw [hword]
    simp [diagonalCount, List.count_append]
  have hlen : (U ++ s :: t :: (V ++ [diagonal])).length = R.length + 1 := by
    rw [hword]
    simp [List.length_append]
  have hUend := Step.endpointFrom_noEast 0 0 U hU
  have hRend := Step.endpointFrom_noEast 0 0 R hR
  have hgap := h.gap
  simp only [Nat.zero_add] at hUend hRend ⊢
  change (endpointFrom 0 0 U).2 = (endpointFrom 0 0 R).1 ∧
    (endpointFrom 0 0 R).1 + 1 < (endpointFrom 0 0 R).2
  rw [hUend, hRend]
  constructor <;> lia

end BounceSeed
end VerticalStripLLT

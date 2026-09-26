import VerticalStripLLT.BounceDecompositionProperties
import VerticalStripLLT.BounceCoordinates

namespace VerticalStripLLT

theorem BounceSeed.raiseFinal {A : List Step}
    (h : BounceSeed (A ++ [Step.diagonal])) :
    BounceSeed (A ++ Step.north :: [Step.diagonal]) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using h.noEast
  · exact ⟨A ++ [Step.north], by simp [List.append_assoc]⟩
  · have hc : Step.diagonalCount (A ++ Step.north :: [Step.diagonal]) =
        Step.diagonalCount (A ++ [Step.diagonal]) := by
      simp [Step.diagonalCount, List.count_append]
    have hl : (A ++ Step.north :: [Step.diagonal]).length =
        (A ++ [Step.diagonal]).length + 1 := by simp
    rw [hc, hl]
    exact Nat.lt_succ_of_lt h.gap

theorem BounceSeed.final_gap {A : List Step}
    (h : BounceSeed (A ++ [Step.diagonal])) :
    (Step.endpointFrom 0 0 A).1 + 1 < (Step.endpointFrom 0 0 A).2 := by
  have hA : Step.east ∉ A := by
    intro he
    apply h.noEast
    simp [he]
  have he := Step.endpointFrom_noEast 0 0 A hA
  rw [he]
  simp only [Nat.zero_add]
  change Step.diagonalCount A + 1 < A.length
  have hg := h.gap
  simpa [Step.diagonalCount, List.count_append, List.length_append] using hg

theorem BounceSeed.dd_length_lt {A V : List Step} :
    (A ++ [Step.diagonal]).length <
      (A ++ Step.diagonal :: Step.diagonal :: (V ++ [Step.diagonal])).length := by
  simp [List.length_append]

theorem BounceSeed.raise_length_lt {A V : List Step} :
    (A ++ Step.north :: [Step.diagonal]).length <
      (A ++ Step.diagonal :: Step.diagonal :: (V ++ [Step.diagonal])).length := by
  simp [List.length_append]

theorem BounceDecomposition.corner_lt {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t)
    (hd : s = Step.diagonal ∨ t = Step.diagonal) :
    (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2 := by
  induction h with
  | @stop U V s t hs ht hdd hU hV hreturn =>
      have hc : Step.diagonalCount U < U.length := by
        rcases hd with hsd | htd
        · subst s
          simp only [Step.diagonalCount, List.count_append, List.count_cons,
            List.count_nil] at hreturn ⊢
          lia
        · subst t
          simp only [Step.diagonalCount, List.count_append, List.count_cons,
            List.count_nil] at hreturn ⊢
          lia
      have hu := Step.endpointFrom_noEast 0 0 U hU
      rw [hu]
      simp only [Nat.zero_add]
      lia
  | descend hV hreturn child ih =>
      exact ih hd

end VerticalStripLLT

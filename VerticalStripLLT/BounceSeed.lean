import VerticalStripLLT.WordCounts

namespace VerticalStripLLT

open Step

structure BounceSeed (Y : List Step) : Prop where
  noEast : east ∉ Y
  lastD : ∃ U, Y = U ++ [diagonal]
  gap : diagonalCount Y + 1 < Y.length

theorem BounceSeed.dd_child (U V : List Step)
    (h : BounceSeed (U ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hindex : U.length + 1 = diagonalCount
      (U ++ diagonal :: diagonal :: (V ++ [diagonal]))) :
    BounceSeed (U ++ [diagonal]) ∧
      (U ++ [diagonal]).length <
        (U ++ diagonal :: diagonal :: (V ++ [diagonal])).length := by
  have hno : east ∉ U ++ [diagonal] := by
    intro he
    apply h.noEast
    simp at he ⊢
    exact Or.inl he
  have hlast : ∃ T, U ++ [diagonal] = T ++ [diagonal] :=
    ⟨U, by simp⟩
  have hgap : diagonalCount (U ++ [diagonal]) + 1 <
      (U ++ [diagonal]).length := by
    have hg := h.gap
    simp [diagonalCount, List.count_append, List.length_append] at hg hindex ⊢
    lia
  have hlen : (U ++ [diagonal]).length <
      (U ++ diagonal :: diagonal :: (V ++ [diagonal])).length := by
    simp [List.length_append]
  exact ⟨⟨hno, hlast, hgap⟩, hlen⟩

theorem BounceSeed.split (Y : List Step) (h : BounceSeed Y) :
    ∃ (U : List Step) (s t : Step) (V : List Step),
      Y = U ++ s :: t :: (V ++ [diagonal]) ∧
      U.length + 1 = diagonalCount Y ∧
      s ≠ east ∧ t ≠ east ∧ east ∉ U ∧ east ∉ V := by
  obtain ⟨T, hY⟩ := h.lastD
  have hg := h.gap
  rw [hY] at hg
  simp [diagonalCount, List.count_append, List.length_append] at hg
  have hlen : diagonalCount T + 2 ≤ T.length := by
    unfold diagonalCount
    lia
  have hk : diagonalCount T ≤ T.length := by lia
  let D := T.drop (diagonalCount T)
  have hTD : T = T.take (diagonalCount T) ++ D := by
    exact (List.take_append_drop (diagonalCount T) T).symm
  cases hd : D with
  | nil =>
      have hdrop : D.length = T.length - diagonalCount T := by
        simp [D]
      simp only [hd, List.length_nil] at hdrop
      lia
  | cons s R =>
      cases hr : R with
      | nil =>
          have hdrop : D.length = T.length - diagonalCount T := by
            simp [D]
          simp [hd, hr] at hdrop
          lia
      | cons t V =>
          have hneT : east ∉ T := by
            intro heT
            apply h.noEast
            simpa [hY] using heT
          have hneD : east ∉ D := by
            intro heD
            apply hneT
            exact List.mem_of_mem_drop heD
          have hneParts' : east ≠ s ∧ east ≠ t ∧ east ∉ V := by
            simpa [hd, hr] using hneD
          have hneParts : s ≠ east ∧ t ≠ east ∧ east ∉ V :=
            ⟨hneParts'.1.symm, hneParts'.2.1.symm, hneParts'.2.2⟩
          have hneU : east ∉ T.take (diagonalCount T) := by
            intro heU
            apply hneT
            exact List.mem_of_mem_take heU
          refine ⟨T.take (diagonalCount T), s, t, V, ?_, ?_,
            hneParts.1, hneParts.2.1, hneU, hneParts.2.2⟩
          · have hTD' := congrArg (fun Z => Z ++ [diagonal]) hTD
            calc
              Y = T ++ [diagonal] := hY
              _ = (T.take (diagonalCount T) ++ D) ++ [diagonal] := hTD'
              _ = T.take (diagonalCount T) ++ s :: t :: (V ++ [diagonal]) := by
                rw [hd, hr]
                simp [List.append_assoc]
          · rw [List.length_take_of_le hk]
            simp [hY, diagonalCount, List.count_append]

end VerticalStripLLT

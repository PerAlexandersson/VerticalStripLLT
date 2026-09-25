import VerticalStripLLT.BounceDecomposition

namespace VerticalStripLLT

theorem BounceDecomposition.parts {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t) :
    s ≠ Step.east ∧ t ≠ Step.east ∧
      ¬(s = Step.diagonal ∧ t = Step.diagonal) ∧
      Step.east ∉ U ∧ Step.east ∉ V := by
  induction h with
  | stop hs ht hdd hU hV hreturn => exact ⟨hs, ht, hdd, hU, hV⟩
  | descend hV hreturn child ih =>
      exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1,
        by simpa using And.intro ih.2.2.2.2 hV⟩

theorem BounceDecomposition.noEast_left {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t) : Step.east ∉ U := h.parts.2.2.2.1

theorem BounceDecomposition.noEast_right {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t) : Step.east ∉ V := h.parts.2.2.2.2

theorem BounceDecomposition.raiseFinal_word {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t) :
    BounceDecomposition (U ++ s :: t :: ((V ++ [Step.north]) ++ [Step.diagonal])) U
      (V ++ [Step.north]) s t := by
  cases h with
  | stop hs ht hdd hU hV hreturn =>
      refine .stop hs ht hdd hU (by simpa using hV) ?_
      simpa [Step.diagonalCount, List.count_cons, List.count_append] using hreturn
  | @descend A V₀ V₁ U s t hV hreturn child =>
      have hA : A = U ++ s :: t :: V₀ := by
        apply List.append_cancel_right (bs := [Step.diagonal])
        simpa only [List.append_assoc, List.cons_append] using child.word_eq
      have hr : A.length + 1 = Step.diagonalCount
          (A ++ Step.diagonal :: Step.diagonal ::
            ((V₁ ++ [Step.north]) ++ [Step.diagonal])) := by
        simpa [Step.diagonalCount, List.count_cons, List.count_append] using hreturn
      have hc := BounceDecomposition.descend
        (V₁ := V₁ ++ [Step.north]) (by simpa using hV) hr child
      simpa only [hA, List.append_assoc, List.cons_append] using hc

theorem BounceDecomposition.raiseFinal {A U V : List Step} {s t : Step}
    (h : BounceDecomposition (A ++ [Step.diagonal]) U V s t) :
    BounceDecomposition (A ++ Step.north :: [Step.diagonal]) U
      (V ++ [Step.north]) s t := by
  have hA : A = U ++ s :: t :: V := by
    apply List.append_cancel_right (bs := [Step.diagonal])
    simpa only [List.append_assoc, List.cons_append] using h.word_eq
  simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using
    h.raiseFinal_word

end VerticalStripLLT

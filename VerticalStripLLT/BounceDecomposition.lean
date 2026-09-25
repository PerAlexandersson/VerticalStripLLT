import VerticalStripLLT.BounceTrace

namespace VerticalStripLLT

inductive BounceDecomposition : List Step → List Step → List Step → Step → Step → Prop where
  | stop {U V : List Step} {s t : Step}
      (hs : s ≠ Step.east) (ht : t ≠ Step.east)
      (hdd : ¬(s = Step.diagonal ∧ t = Step.diagonal))
      (hU : Step.east ∉ U) (hV : Step.east ∉ V)
      (hreturn : U.length + 1 = Step.diagonalCount
        (U ++ s :: t :: (V ++ [Step.diagonal])))
      : BounceDecomposition (U ++ s :: t :: (V ++ [Step.diagonal])) U V s t
  | descend {A V₀ V₁ U : List Step} {s t : Step}
      (hV₁ : Step.east ∉ V₁)
      (hreturn : A.length + 1 = Step.diagonalCount
        (A ++ Step.diagonal :: Step.diagonal :: (V₁ ++ [Step.diagonal])))
      (child : BounceDecomposition (A ++ [Step.diagonal]) U V₀ s t)
      : BounceDecomposition (A ++ Step.diagonal :: Step.diagonal ::
        (V₁ ++ [Step.diagonal])) U (V₀ ++ Step.diagonal :: Step.diagonal :: V₁) s t

theorem BounceDecomposition.word_eq {Y U V : List Step} {s t : Step}
    (h : BounceDecomposition Y U V s t) :
    Y = U ++ s :: t :: (V ++ [Step.diagonal]) := by
  induction h with
  | @stop U V s t hs ht hdd hU hV hreturn => rfl
  | @descend A V₀ V₁ U s t hV hreturn child ih =>
      simpa [List.append_assoc] using congrArg
        (fun Z => Z ++ Step.diagonal :: (V₁ ++ [Step.diagonal])) ih

theorem BounceTrace.decompose {Y : List Step} (h : BounceTrace Y) :
    ∃ U V s t, BounceDecomposition Y U V s t := by
  induction h with
  | stop hs ht hdd hU hV hreturn =>
      exact ⟨_, _, _, _, .stop hs ht hdd hU hV hreturn⟩
  | descend hV hreturn child ih =>
      rcases ih with ⟨U, V₀, s, t, hd⟩
      exact ⟨U, V₀ ++ Step.diagonal :: Step.diagonal :: _, s, t,
        .descend hV hreturn hd⟩

end VerticalStripLLT

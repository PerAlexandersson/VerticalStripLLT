import VerticalStripLLT.BounceSeed

namespace VerticalStripLLT

inductive BounceTrace : List Step → Prop where
  | stop {U V : List Step} {s t : Step}
      (hs : s ≠ Step.east) (ht : t ≠ Step.east)
      (hdd : ¬(s = Step.diagonal ∧ t = Step.diagonal))
      (hU : Step.east ∉ U) (hV : Step.east ∉ V)
      (hreturn : U.length + 1 = Step.diagonalCount
        (U ++ s :: t :: (V ++ [Step.diagonal]))) :
      BounceTrace (U ++ s :: t :: (V ++ [Step.diagonal]))
  | descend {U V : List Step}
      (hV : Step.east ∉ V)
      (hreturn : U.length + 1 = Step.diagonalCount
        (U ++ Step.diagonal :: Step.diagonal :: (V ++ [Step.diagonal])))
      (child : BounceTrace (U ++ [Step.diagonal])) :
      BounceTrace (U ++ Step.diagonal :: Step.diagonal :: (V ++ [Step.diagonal]))

theorem BounceSeed.trace {Y : List Step} (h : BounceSeed Y) : BounceTrace Y := by
  suffices ∀ m (Z : List Step), Z.length = m → BounceSeed Z → BounceTrace Z from
    this Y.length Y rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Z hlen hZ
      obtain ⟨U, s, t, V, hsplit, hreturn, hs, ht, hU, hV⟩ := BounceSeed.split Z hZ
      subst Z
      by_cases hdd : s = Step.diagonal ∧ t = Step.diagonal
      · rcases hdd with ⟨rfl, rfl⟩
        have hchild := BounceSeed.dd_child U V hZ hreturn
        have hchildTrace : BounceTrace (U ++ [Step.diagonal]) :=
          ih _ (by simpa only [hlen] using hchild.2) _ rfl hchild.1
        exact BounceTrace.descend hV hreturn hchildTrace
      · exact BounceTrace.stop hs ht hdd hU hV hreturn

end VerticalStripLLT

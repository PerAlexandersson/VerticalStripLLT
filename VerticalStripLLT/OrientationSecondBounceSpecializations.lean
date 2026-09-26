import VerticalStripLLT.OrientationSecondBounce

namespace VerticalStripLLT

theorem orientationExpansion_secondBounce_general {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: V)).2) :
    orientationExpansion
        (⟨(U ++ Step.diagonal :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W, h⟩ : SchroderPath n) =
      orientationExpansion
        (SchroderPath.secondBounceSuccessor U V W h hgap) := by
  exact orientationExpansionAt_secondBounce_general U V W h hreturn hgap
    (Polynomial.X - 1)

theorem shiftedOrientationExpansion_secondBounce_general {n : ℕ}
    (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.diagonal :: Step.north :: V)).2) :
    shiftedOrientationExpansion
        (⟨(U ++ Step.diagonal :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W, h⟩ : SchroderPath n) =
      shiftedOrientationExpansion
        (SchroderPath.secondBounceSuccessor U V W h hgap) := by
  exact orientationExpansionAt_secondBounce_general U V W h hreturn hgap
    Polynomial.X

end VerticalStripLLT

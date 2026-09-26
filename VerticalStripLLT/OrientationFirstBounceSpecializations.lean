import VerticalStripLLT.OrientationFirstBounce

namespace VerticalStripLLT

theorem orientationExpansion_firstBounce_general {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.north :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.north :: V)).2) :
    orientationExpansion
        (⟨(U ++ Step.north :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W, h⟩ : SchroderPath n) =
      MvPolynomial.C Polynomial.X * orientationExpansion
        (SchroderPath.swapDiagonalEast
          (U ++ Step.north :: Step.north :: V) W h hgap) := by
  have hC : (MvPolynomial.C (Polynomial.X - 1 + 1) : EExpansion) =
      MvPolynomial.C Polynomial.X := by rw [sub_add_cancel]
  exact (orientationExpansionAt_firstBounce_general U V W h hreturn hgap
    (Polynomial.X - 1)).trans (congrArg (fun a : EExpansion => a *
      orientationExpansion (SchroderPath.swapDiagonalEast
        (U ++ Step.north :: Step.north :: V) W h hgap)) hC)

theorem shiftedOrientationExpansion_firstBounce_general {n : ℕ}
    (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.north :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.north :: V)).2) :
    shiftedOrientationExpansion
        (⟨(U ++ Step.north :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W, h⟩ : SchroderPath n) =
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion
        (SchroderPath.swapDiagonalEast
          (U ++ Step.north :: Step.north :: V) W h hgap) := by
  simpa only [shiftedOrientationExpansion] using
    orientationExpansionAt_firstBounce_general U V W h hreturn hgap
      Polynomial.X

end VerticalStripLLT

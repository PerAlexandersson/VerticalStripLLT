import VerticalStripLLT.BounceAssembly
import VerticalStripLLT.OrientationUnicellular
namespace VerticalStripLLT
theorem orientationExpansionAt_firstBounce_general {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).2)
    (z : Q) :
    orientationExpansionAt
      (⟨(U ++ Step.north :: Step.north :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
        SchroderPath n) z =
      MvPolynomial.C (z + 1) *
        orientationExpansionAt (SchroderPath.swapDiagonalEast
          (U ++ Step.north :: Step.north :: V) W h hgap) z := by
  refine BounceHRV.orientationExpansionAt_bounce_core
    (B := SchroderPath.firstBounceBase _ W h hgap) (i := SchroderPath.firstBounceLow _ W h)
    (y := SchroderPath.firstBounceMid _ W h hgap) (t := SchroderPath.firstBounceTop _ W h)
    rfl hgap
    (SchroderPath.firstBounce_low_mid_mem _ W h hgap)
    (SchroderPath.firstBounce_strict_swap_invariant U V W h hreturn hgap)
    (SchroderPath.firstBounce_normal_erase_swap_invariant U V W h hreturn hgap)
    (SchroderPath.firstBounce_fresh _ W h hgap)
    (SchroderPath.firstBounce_source_normal _ W h hgap)
    (SchroderPath.firstBounce_source_strict _ W h hgap)
    (SchroderPath.firstBounce_succ_normal _ W h hgap).symm
    (SchroderPath.firstBounce_succ_strict _ W h hgap) z

end VerticalStripLLT

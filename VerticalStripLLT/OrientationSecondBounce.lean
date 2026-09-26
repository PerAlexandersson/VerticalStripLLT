import VerticalStripLLT.SecondBounceAssembly
import VerticalStripLLT.OrientationFirstBounce
namespace VerticalStripLLT
theorem orientationExpansionAt_secondBounce_general {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2)
    (z : Q) :
    orientationExpansionAt
      (⟨(U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
        SchroderPath n) z =
      orientationExpansionAt (SchroderPath.secondBounceSuccessor U V W h hgap) z := by
  have hy : (SchroderPath.secondBounceMid U V W h hgap).val =
      (SchroderPath.secondBounceLow U V W h).val + 1 := by
    rw [SchroderPath.secondBounceMid_val, SchroderPath.secondBounceLow_val]
  have hyt : SchroderPath.secondBounceMid U V W h hgap < SchroderPath.secondBounceTop U V W h := by
    rw [Fin.lt_def, SchroderPath.secondBounceMid_val, SchroderPath.secondBounceTop_val]
    exact hgap
  have hai : SchroderPath.secondBounceCorner U V W h < SchroderPath.secondBounceLow U V W h := by
    rw [Fin.lt_def, SchroderPath.secondBounceLow_val, ← hreturn]
    exact (SchroderPath.secondBounce_corner_lt U V W h).1
  exact BounceHRV.orientationExpansionAt_secondBounce_core hy hyt hai
    (SchroderPath.secondBounce_low_mid_mem U V W h hgap)
    (SchroderPath.secondBounce_strict_swap_invariant U V W h hreturn hgap)
    (SchroderPath.secondBounce_normal_erase_swap_invariant U V W h hreturn hgap)
    (SchroderPath.secondBounce_fresh_top U V W h hgap)
    (SchroderPath.secondBounce_source_normal U V W h hgap)
    (SchroderPath.secondBounce_source_strict U V W h hreturn hgap)
    (SchroderPath.secondBounce_fresh_corner U V W h hreturn hgap)
    (SchroderPath.secondBounce_target_normal U V W h hreturn hgap)
    (SchroderPath.secondBounce_target_strict U V W h hreturn hgap) z

end VerticalStripLLT

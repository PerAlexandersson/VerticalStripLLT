import VerticalStripLLT.FirstBounceGraph
import VerticalStripLLT.BounceWeight

open scoped BigOperators

namespace VerticalStripLLT

-- Keep the no-east hypothesis in the manuscript-facing interface.
set_option linter.unusedVariables false in
open SchroderPath in
theorem coloringLLT_firstBounce {n : ℕ} (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.north :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).2)
    (m : ℕ) :
    coloringLLT
      (⟨(U ++ Step.north :: Step.north :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
        SchroderPath n) m =
      MvPolynomial.C Polynomial.X *
        coloringLLT (SchroderPath.swapDiagonalEast
          (U ++ Step.north :: Step.north :: V) W h hgap) m := by
  have hzi : firstBounceTop _ W h ≠ firstBounceLow _ W h := by
    intro hEq
    have := congrArg Fin.val hEq
    simp only [firstBounceTop, firstBounceLow] at this
    lia
  have hzy : firstBounceTop _ W h ≠ firstBounceMid _ W h hgap := by
    intro hEq
    have := congrArg Fin.val hEq
    simp only [firstBounceTop, firstBounceMid] at this
    lia
  exact coloringLLT_eq_C_X_mul_of_edges _ _ (firstBounceBase _ W h hgap)
    (firstBounceLow _ W h) (firstBounceMid _ W h hgap) (firstBounceTop _ W h)
    (firstBounce_source_normal _ W h hgap) (firstBounce_source_strict _ W h hgap)
    (firstBounce_succ_normal _ W h hgap) (firstBounce_succ_strict _ W h hgap)
    (firstBounce_fresh _ W h hgap) (firstBounce_low_mid_mem _ W h hgap)
    (firstBounce_strict_swap_invariant U V W h hreturn hgap)
    (firstBounce_normal_erase_swap_invariant U V W h hreturn hgap) hzi hzy

end VerticalStripLLT

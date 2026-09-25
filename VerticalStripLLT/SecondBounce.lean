import VerticalStripLLT.SecondBounceGraph
import VerticalStripLLT.SecondBounceWeight

open scoped BigOperators

namespace VerticalStripLLT

-- Keep the no-east hypothesis in the manuscript-facing interface.
set_option linter.unusedVariables false in
open SchroderPath in
theorem coloringLLT_secondBounce {n : ℕ} (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2)
    (m : ℕ) :
    coloringLLT
      (⟨(U ++ Step.diagonal :: Step.north :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
        SchroderPath n) m =
      coloringLLT (SchroderPath.secondBounceSuccessor U V W h hgap) m := by
  have hlt := (secondBounce_corner_lt U V W h).1
  have hL := secondBounceLow_val U V W h
  have hM := secondBounceMid_val U V W h hgap
  have hT := secondBounceTop_val U V W h
  have ha : (secondBounceCorner U V W h).val = (Step.endpointFrom 0 0 U).1 := rfl
  have hai : secondBounceCorner U V W h ≠ secondBounceLow U V W h := fun hEq => by
    have := congrArg Fin.val hEq
    lia
  have hay : secondBounceCorner U V W h ≠ secondBounceMid U V W h hgap := fun hEq => by
    have := congrArg Fin.val hEq
    lia
  have hzi : secondBounceTop U V W h ≠ secondBounceLow U V W h := fun hEq => by
    have := congrArg Fin.val hEq
    lia
  have hzy : secondBounceTop U V W h ≠ secondBounceMid U V W h hgap := fun hEq => by
    have := congrArg Fin.val hEq
    lia
  exact coloringLLT_eq_of_secondBounce_edges _ _ (secondBounceBase U V W h hgap)
    (secondBounceCorner U V W h) (secondBounceLow U V W h) (secondBounceMid U V W h hgap)
    (secondBounceTop U V W h)
    (secondBounce_source_normal U V W h hgap)
    (secondBounce_source_strict U V W h hreturn hgap)
    (secondBounce_target_normal U V W h hreturn hgap)
    (secondBounce_target_strict U V W h hreturn hgap)
    (secondBounce_fresh_top U V W h hgap)
    (secondBounce_fresh_corner U V W h hreturn hgap)
    (secondBounce_low_mid_mem U V W h hgap)
    (secondBounce_strict_swap_invariant U V W h hreturn hgap)
    (secondBounce_normal_erase_swap_invariant U V W h hreturn hgap)
    hai hay hzi hzy

end VerticalStripLLT

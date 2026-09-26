import VerticalStripLLT.WordEvaluation
import VerticalStripLLT.ReductionThirdBounce

namespace VerticalStripLLT

theorem thirdBounce_word {A : Type*} [CommRing A] [IsDomain A]
    {q : A} {e : ℕ → A} {F : ∀ n, SchroderPath n → A}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.diagonal :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.diagonal :: V)).1)
    (hgap : (Step.endpointFrom 0 0
      (U ++ Step.north :: Step.diagonal :: V)).1 + 1 <
      (Step.endpointFrom 0 0
        (U ++ Step.north :: Step.diagonal :: V)).2) :
    SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.diagonal :: V) ++
          Step.diagonal :: Step.east :: W) =
      (q - 1) * SchroderPath.evalWord F n
          ((U ++ Step.north :: Step.diagonal :: V) ++
            Step.east :: Step.diagonal :: W) +
        q * SchroderPath.evalWord F n
          ((U ++ Step.diagonal :: Step.north :: V) ++
            Step.east :: Step.diagonal :: W) := by
  obtain ⟨Q, R, hQ, hR, hEq⟩ :=
    SatisfiesReductionRecursion.thirdBounce H hq U V W hV h hreturn hgap
  rw [SchroderPath.evalWord_of_valid F n _ h]
  rw [← hQ, ← hR]
  rw [SchroderPath.evalWord_steps F Q, SchroderPath.evalWord_steps F R]
  exact hEq

end VerticalStripLLT

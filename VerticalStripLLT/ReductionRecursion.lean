import VerticalStripLLT.Recursion

namespace VerticalStripLLT

set_option linter.unusedVariables false in
/-- A sufficient certificate for the concrete expansion proof.
The two leading-east clauses are additional; `SatisfiesRecursion` is unchanged. -/
structure SatisfiesReductionRecursion {A : Type*} [CommRing A] (q : A)
    (e : ℕ → A) (F : ∀ n, SchroderPath n → A) : Prop
    extends SatisfiesRecursion q e F where
  /-- The additional first-bounce clause with a leading east in the middle. -/
  firstBounceOneLeadingEast : ∀ {n} (U V W : List Step)
      (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
      (h : Step.validFrom n 0 0
        ((U ++ Step.north :: Step.north :: Step.east :: V) ++
          Step.diagonal :: Step.east :: W) = true)
      (hreturn : (Step.endpointFrom 0 0 U).2 =
        (Step.endpointFrom 0 0
          (U ++ Step.north :: Step.north :: Step.east :: V)).1)
      (hgap : (Step.endpointFrom 0 0
          (U ++ Step.north :: Step.north :: Step.east :: V)).1 + 1 <
        (Step.endpointFrom 0 0
          (U ++ Step.north :: Step.north :: Step.east :: V)).2),
    F n ⟨(U ++ Step.north :: Step.north :: Step.east :: V) ++
        Step.diagonal :: Step.east :: W, h⟩ =
      q * F n (SchroderPath.swapDiagonalEast
        (U ++ Step.north :: Step.north :: Step.east :: V) W h hgap)
  /-- The corresponding second-bounce clause with a leading east in the middle. -/
  secondBounceOneLeadingEast : ∀ {n} (U V W : List Step)
      (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
      (h : Step.validFrom n 0 0
        ((U ++ Step.diagonal :: Step.north :: Step.east :: V) ++
          Step.diagonal :: Step.east :: W) = true)
      (hreturn : (Step.endpointFrom 0 0 U).2 =
        (Step.endpointFrom 0 0
          (U ++ Step.diagonal :: Step.north :: Step.east :: V)).1)
      (hgap : (Step.endpointFrom 0 0
          (U ++ Step.diagonal :: Step.north :: Step.east :: V)).1 + 1 <
        (Step.endpointFrom 0 0
          (U ++ Step.diagonal :: Step.north :: Step.east :: V)).2),
    F n ⟨(U ++ Step.diagonal :: Step.north :: Step.east :: V) ++
        Step.diagonal :: Step.east :: W, h⟩ =
      F n (SchroderPath.secondBounceSuccessor U (Step.east :: V) W h hgap)

end VerticalStripLLT

import VerticalStripLLT.Column
import VerticalStripLLT.Concat
import VerticalStripLLT.UnicellularPath
import VerticalStripLLT.BouncePath
import VerticalStripLLT.SecondBouncePath

namespace VerticalStripLLT

open SchroderPath

-- The word certificates retain named hypotheses for matching the source clauses.
set_option linter.unusedVariables false in
structure SatisfiesRecursion {A : Type*} [CommRing A] (q : A) (e : ℕ → A)
    (F : ∀ n, SchroderPath n → A) : Prop where
  empty : F 0 SchroderPath.empty = 1
  column : ∀ k, F (k + 1) (SchroderPath.column k) = e (k + 1)
  concat : ∀ {n k} (P : SchroderPath n) (Q : SchroderPath k),
    F (n + k) (P.concat Q) = F n P * F k Q
  unicellular : ∀ {n} (U V : List Step)
      (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true),
    F n (SchroderPath.resolveNorthEast U V h) -
        F n (SchroderPath.resolveEastNorth U V h) =
      (q - 1) * F n ⟨U ++ Step.diagonal :: V, h⟩
  firstBounce : ∀ {n} (U V W : List Step)
      (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
      (h : Step.validFrom n 0 0
        ((U ++ Step.north :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W) = true)
      (hreturn : (Step.endpointFrom 0 0 U).2 =
        (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1)
      (hgap : (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).1 + 1 <
        (Step.endpointFrom 0 0 (U ++ Step.north :: Step.north :: V)).2),
    F n ⟨(U ++ Step.north :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W, h⟩ =
      q * F n (SchroderPath.swapDiagonalEast
        (U ++ Step.north :: Step.north :: V) W h hgap)
  secondBounce : ∀ {n} (U V W : List Step)
      (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
      (h : Step.validFrom n 0 0
        ((U ++ Step.diagonal :: Step.north :: V) ++
          Step.diagonal :: Step.east :: W) = true)
      (hreturn : (Step.endpointFrom 0 0 U).2 =
        (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1)
      (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
        (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2),
    F n ⟨(U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W, h⟩ =
      F n (secondBounceSuccessor U V W h hgap)

end VerticalStripLLT

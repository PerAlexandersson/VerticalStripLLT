import VerticalStripLLT.Recursion
import VerticalStripLLT.NorthEastReduction

namespace VerticalStripLLT

theorem firstEast_north_reduction {A : Type*} [CommRing A] (q : A)
    (e : ℕ → A) (F : ∀ n, SchroderPath n → A)
    (hF : SatisfiesRecursion q e F) {n : ℕ} (U W : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.north :: Step.east :: W) = true)
    (hU : Step.east ∉ U)
    (hgap : (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2) :
    ∃ P Q : SchroderPath n,
      P.steps = U ++ Step.diagonal :: W ∧
      Q.steps = U ++ Step.east :: Step.north :: W ∧
      Step.eastCount (U ++ Step.north :: Step.east :: W) =
        Step.eastCount P.steps + 1 ∧
      Step.eastCount (U ++ Step.north :: Step.east :: W) =
        Step.eastCount Q.steps ∧
      Step.firstEastHeight (U ++ Step.north :: Step.east :: W) =
        Step.firstEastHeight Q.steps + 1 ∧
      F n ⟨(U ++ Step.north :: Step.east :: W), h⟩ =
        (q - 1) * F n P + F n Q := by
  let hP := Step.validFrom_contractNorthEast n 0 0 h hgap
  let P : SchroderPath n :=
    ⟨U ++ Step.diagonal :: W, hP⟩
  let Q : SchroderPath n :=
    SchroderPath.swapNorthEast U W h hgap
  have hP_steps : P.steps = U ++ Step.diagonal :: W := rfl
  have hQ_steps : Q.steps = U ++ Step.east :: Step.north :: W := rfl
  have hu := hF.unicellular (U := U) (V := W) hP
  have hne : SchroderPath.resolveNorthEast U W hP =
      (⟨U ++ Step.north :: Step.east :: W, h⟩ : SchroderPath n) := by
    rfl
  have hse : SchroderPath.resolveEastNorth U W hP = Q := by
    rfl
  rw [hne, hse] at hu
  refine ⟨P, Q, hP_steps, hQ_steps, ?_, ?_, ?_, ?_⟩
  · simpa [hP_steps] using Step.eastCount_northEast_contract U W
  · simpa [hQ_steps] using Step.eastCount_northEast_swap U W
  · simpa [hQ_steps] using Step.firstEastHeight_northEast_swap U W hU
  · exact sub_eq_iff_eq_add.mp hu

end VerticalStripLLT

import VerticalStripLLT.GeneralizedSecondBounce
import VerticalStripLLT.BounceMeasure

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- The DN generalized bounce with its valid successor and strict height decrease. -/
theorem generalizedSecondBounce {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V Step.diagonal Step.north)
    (hv : Step.validFrom n 0 0 (Y ++ Step.east :: W) = true) :
    ∃ Q : SchroderPath n,
      Q.steps = (U ++ Step.north :: Step.diagonal :: V) ++
        Step.east :: Step.diagonal :: W ∧
      F n ⟨Y ++ Step.east :: W, hv⟩ = F n Q ∧
      Step.eastCount Q.steps = Step.eastCount (Y ++ Step.east :: W) ∧
      Step.firstEastHeight Q.steps <
        Step.firstEastHeight (Y ++ Step.east :: W) := by
  have hY : Y = (U ++ Step.diagonal :: Step.north :: V) ++
      [Step.diagonal] := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hd.word_eq
  have hs : BounceSeed ((U ++ Step.diagonal :: Step.north :: V) ++
      [Step.diagonal]) := hY ▸ hseed
  have hp : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true := by
    simpa only [hY, List.append_assoc, List.cons_append, List.nil_append] using hv
  let Q := SchroderPath.secondBounceSuccessor U V W hp hs.final_gap
  refine ⟨Q, rfl, ?_, ?_, ?_⟩
  · have hg := H.generalizedSecondBounce_word hq hseed hd hv
    rw [SchroderPath.evalWord_of_valid F n _ hv] at hg
    have hQ : SchroderPath.evalWord F n
        ((U ++ Step.north :: Step.diagonal :: V) ++
          Step.east :: Step.diagonal :: W) = F n Q :=
      SchroderPath.evalWord_steps F Q
    rw [hQ] at hg
    exact hg
  · simp [Q, SchroderPath.secondBounceSuccessor_steps, hY, Step.eastCount,
      List.append_assoc]
  · have hno : Step.east ∉ U ++ Step.diagonal :: Step.north :: V := by
      intro he
      exact hs.noEast (List.mem_append_left _ he)
    have hsrc := Step.firstEastHeight_append_east
      (U ++ Step.diagonal :: Step.north :: V ++ [Step.diagonal]) W
      (by simpa [hY] using hseed.noEast)
    have htargetNo : Step.east ∉ U ++ Step.north :: Step.diagonal :: V := by
      simpa using hno
    have hqheight := Step.firstEastHeight_append_east
      (U ++ Step.north :: Step.diagonal :: V)
      (Step.diagonal :: W) htargetNo
    have hheight : Step.firstEastHeight (Y ++ Step.east :: W) =
        Step.firstEastHeight Q.steps + 1 := by
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsrc hqheight
      simp only [Q, SchroderPath.secondBounceSuccessor_steps, hY,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [hsrc, hqheight]
      simp only [Step.endpointFrom_append, Step.endpointFrom] at hsrc ⊢
    rw [hheight]
    exact Nat.lt_succ_self _

end SatisfiesReductionRecursion

end VerticalStripLLT

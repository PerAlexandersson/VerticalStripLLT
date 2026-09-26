import VerticalStripLLT.GeneralizedThirdBounce
import VerticalStripLLT.BounceMeasure

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- The ND generalized bounce with valid successors and strict first-east decreases. -/
theorem generalizedThirdBounce {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V north diagonal)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) :
    ∃ Q R : SchroderPath n,
      Q.steps = (U ++ north :: diagonal :: V) ++ east :: diagonal :: W ∧
      R.steps = (U ++ diagonal :: north :: V) ++ east :: diagonal :: W ∧
      F n ⟨Y ++ east :: W, hv⟩ = (q - 1) * F n Q + q * F n R ∧
      eastCount Q.steps = eastCount (Y ++ east :: W) ∧
      eastCount R.steps = eastCount (Y ++ east :: W) ∧
      firstEastHeight Q.steps < firstEastHeight (Y ++ east :: W) ∧
      firstEastHeight R.steps < firstEastHeight (Y ++ east :: W) := by
  have hY : Y = (U ++ north :: diagonal :: V) ++ [diagonal] := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hd.word_eq
  have hs : BounceSeed ((U ++ north :: diagonal :: V) ++ [diagonal]) := hY ▸ hseed
  have hp : validFrom n 0 0
      ((U ++ north :: diagonal :: V) ++ diagonal :: east :: W) = true := by
    simpa only [hY, List.append_assoc, List.cons_append, List.nil_append] using hv
  let Q := SchroderPath.swapDiagonalEast (U ++ north :: diagonal :: V) W hp hs.final_gap
  have hRvalid : validFrom n 0 0
      ((U ++ diagonal :: north :: V) ++ east :: diagonal :: W) = true :=
    hd.valid_nd_successor hseed hp
  let R : SchroderPath n :=
    ⟨(U ++ diagonal :: north :: V) ++ east :: diagonal :: W, hRvalid⟩
  refine ⟨Q, R, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hg := H.generalizedThirdBounce_word hq hseed hd hv
    rw [SchroderPath.evalWord_of_valid F n _ hv] at hg
    have hQ : SchroderPath.evalWord F n
        ((U ++ north :: diagonal :: V) ++ east :: diagonal :: W) = F n Q :=
      SchroderPath.evalWord_steps F Q
    have hR : SchroderPath.evalWord F n
        ((U ++ diagonal :: north :: V) ++ east :: diagonal :: W) = F n R :=
      SchroderPath.evalWord_steps F R
    rw [hQ, hR] at hg
    exact hg
  · simpa only [Q, SchroderPath.swapDiagonalEast_steps, hY, List.append_assoc,
      List.cons_append, List.nil_append] using
      (eastCount_diagonalEast_swap (U ++ north :: diagonal :: V) W).symm
  · simp [R, hY, eastCount, List.append_assoc]
  · have hno : east ∉ U ++ north :: diagonal :: V := by
      intro he
      exact hs.noEast (List.mem_append_left _ he)
    have hm := firstEastHeight_diagonalEast_swap (U ++ north :: diagonal :: V) W hno
    have hheight : firstEastHeight (Y ++ east :: W) = firstEastHeight Q.steps + 1 := by
      simpa only [Q, SchroderPath.swapDiagonalEast_steps, hY, List.append_assoc,
        List.cons_append, List.nil_append] using hm
    rw [hheight]
    exact Nat.lt_succ_self _
  · have hnoND : east ∉ U ++ north :: diagonal :: V := by
      intro he
      exact hs.noEast (List.mem_append_left _ he)
    have hnoDN : east ∉ U ++ diagonal :: north :: V := by
      simpa using hnoND
    have hsrc := firstEastHeight_append_east
      ((U ++ north :: diagonal :: V) ++ [diagonal]) W hs.noEast
    have hrheight := firstEastHeight_append_east
      (U ++ diagonal :: north :: V) (diagonal :: W) hnoDN
    have hheight : firstEastHeight (Y ++ east :: W) = firstEastHeight R.steps + 1 := by
      simp only [R, hY, List.append_assoc, List.cons_append,
        List.nil_append] at hsrc hrheight ⊢
      rw [hsrc, hrheight]
      simp only [endpointFrom_append, endpointFrom]
    rw [hheight]
    exact Nat.lt_succ_self _

end SatisfiesReductionRecursion

end VerticalStripLLT

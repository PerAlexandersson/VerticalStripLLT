import VerticalStripLLT.WordRecursion
import VerticalStripLLT.BounceDDCoordinates
import VerticalStripLLT.GeneralizedBouncePath
import Mathlib.Tactic.LinearCombination

namespace VerticalStripLLT

namespace SatisfiesReductionRecursion

open Step

/-- A single `diagonal, diagonal` induction step for a generalized bounce seed.
The two supplied equations are the induction hypotheses for the raised and
ordinary terminal replacements. -/
theorem dd_step {K : Type*} [CommRing K] [IsDomain K] {q : K} {e : ℕ → K}
    {F : ∀ n, SchroderPath n → K} (H : SatisfiesReductionRecursion q e F)
    (hq : q - 1 ≠ 0) {n : ℕ} (A B C V W : List Step) (a b : K)
    (hseed : BounceSeed (A ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hindex : A.length + 1 = diagonalCount
      (A ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hvalid : validFrom n 0 0
      (A ++ diagonal :: diagonal :: (V ++ diagonal :: east :: W)) = true)
    (hB : endpointFrom 0 0 B = endpointFrom 0 0 A)
    (hC : endpointFrom 0 0 C = endpointFrom 0 0 A)
    (hOrdB : validFrom n 0 0
      (B ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W)) = true)
    (hOrdC : validFrom n 0 0
      (C ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W)) = true)
    (hTargetB : validFrom n 0 0
      (B ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) = true)
    (hTargetC : validFrom n 0 0
      (C ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) = true)
    (hRaised : SchroderPath.evalWord F n
        (A ++ north :: diagonal :: east :: (V ++ east :: diagonal :: W)) =
      a * SchroderPath.evalWord F n
          (B ++ north :: east :: diagonal :: (V ++ east :: diagonal :: W)) +
        b * SchroderPath.evalWord F n
          (C ++ north :: east :: diagonal :: (V ++ east :: diagonal :: W)))
    (hOrd : SchroderPath.evalWord F n
        (A ++ diagonal :: east :: north :: (V ++ diagonal :: east :: W)) =
      a * SchroderPath.evalWord F n
          (B ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W)) +
        b * SchroderPath.evalWord F n
          (C ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W))) :
    SchroderPath.evalWord F n
        (A ++ diagonal :: diagonal :: (V ++ diagonal :: east :: W)) =
      a * SchroderPath.evalWord F n
          (B ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) +
        b * SchroderPath.evalWord F n
          (C ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) := by
  have hV : ∀ s ∈ V, s = north ∨ s = diagonal := by
    intro s hs
    cases s with
    | north => exact Or.inl rfl
    | diagonal => exact Or.inr rfl
    | east =>
      exfalso
      apply hseed.noEast
      simp [hs]
  obtain ⟨hreturnFirst, hgapFirst⟩ :=
    hseed.dd_leading_second_coordinates hindex
  obtain ⟨hreturnB, hgapB⟩ :=
    hseed.dd_after_ordinary_coordinates hindex hB
  obtain ⟨hreturnC, hgapC⟩ :=
    hseed.dd_after_ordinary_coordinates hindex hC
  have hRootD : validFrom n 0 0
      ((A ++ [diagonal]) ++ diagonal :: (V ++ diagonal :: east :: W)) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using hvalid
  have hNEvalid : validFrom n 0 0
      ((A ++ diagonal :: north :: east :: V) ++ diagonal :: east :: W) = true := by
    have hresolve := validFrom_resolve n 0 0
      (U := A ++ [diagonal]) (V := V ++ diagonal :: east :: W) hRootD
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using hresolve.1
  have hOrdB' : validFrom n 0 0
      (((B ++ [east]) ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using hOrdB
  have hOrdC' : validFrom n 0 0
      (((C ++ [east]) ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using hOrdC
  have uRoot : SchroderPath.evalWord F n
      (A ++ diagonal :: north :: east :: (V ++ diagonal :: east :: W)) -
        SchroderPath.evalWord F n
          (A ++ diagonal :: east :: north :: (V ++ diagonal :: east :: W)) =
      (q - 1) * SchroderPath.evalWord F n
      (A ++ diagonal :: diagonal :: (V ++ diagonal :: east :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      unicellular_word H (A ++ [diagonal])
        (V ++ diagonal :: east :: W) hRootD
  have fFirst : SchroderPath.evalWord F n
      (A ++ diagonal :: north :: east :: (V ++ diagonal :: east :: W)) =
      SchroderPath.evalWord F n
        (A ++ north :: diagonal :: east :: (V ++ east :: diagonal :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      secondBounceOneLeadingEast_word H A V W hV hNEvalid hreturnFirst hgapFirst
  have fB : SchroderPath.evalWord F n
      (B ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W)) =
      SchroderPath.evalWord F n
        (B ++ east :: north :: diagonal :: (V ++ east :: diagonal :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      secondBounce_word H (B ++ [east]) V W hV hOrdB' hreturnB hgapB
  have fC : SchroderPath.evalWord F n
      (C ++ east :: diagonal :: north :: (V ++ diagonal :: east :: W)) =
      SchroderPath.evalWord F n
        (C ++ east :: north :: diagonal :: (V ++ east :: diagonal :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      secondBounce_word H (C ++ [east]) V W hV hOrdC' hreturnC hgapC
  have uB : SchroderPath.evalWord F n
      (B ++ north :: east :: diagonal :: (V ++ east :: diagonal :: W)) -
        SchroderPath.evalWord F n
          (B ++ east :: north :: diagonal :: (V ++ east :: diagonal :: W)) =
      (q - 1) * SchroderPath.evalWord F n
        (B ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      unicellular_word H B (diagonal :: (V ++ east :: diagonal :: W)) hTargetB
  have uC : SchroderPath.evalWord F n
      (C ++ north :: east :: diagonal :: (V ++ east :: diagonal :: W)) -
        SchroderPath.evalWord F n
          (C ++ east :: north :: diagonal :: (V ++ east :: diagonal :: W)) =
      (q - 1) * SchroderPath.evalWord F n
        (C ++ diagonal :: diagonal :: (V ++ east :: diagonal :: W)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using
      unicellular_word H C (diagonal :: (V ++ east :: diagonal :: W)) hTargetC
  apply mul_left_cancel₀ hq
  linear_combination -uRoot + fFirst + hRaised - hOrd - a * fB - b * fC +
    a * uB + b * uC

end SatisfiesReductionRecursion

end VerticalStripLLT

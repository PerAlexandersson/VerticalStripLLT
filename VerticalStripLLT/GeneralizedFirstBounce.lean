import VerticalStripLLT.GeneralizedBounceDD
import VerticalStripLLT.BounceMeasure

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- The NN generalized bounce, proved by strong induction on the east-free prefix. -/
theorem generalizedFirstBounce_word {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V north north)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) :
    SchroderPath.evalWord F n (Y ++ east :: W) =
      q * SchroderPath.evalWord F n ((U ++ north :: north :: V) ++ east :: diagonal :: W) := by
  suffices ∀ k (Z : List Step), Z.length = k →
      ∀ {n : ℕ} (U V W : List Step), BounceSeed Z →
        BounceDecomposition Z U V north north →
        validFrom n 0 0 (Z ++ east :: W) = true →
        SchroderPath.evalWord F n (Z ++ east :: W) =
          q * SchroderPath.evalWord F n
            ((U ++ north :: north :: V) ++ east :: diagonal :: W) from
    this Y.length Y rfl U V W hseed hd hv
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro Z hlen n U V W hseed hd hv
      cases hd with
      | stop hs ht hdd hU hV hreturn =>
          have hallowed : ∀ s ∈ V, s = north ∨ s = diagonal := by
            intro s hs
            cases s with
            | north => exact Or.inl rfl
            | diagonal => exact Or.inr rfl
            | east => exact False.elim (hV hs)
          have hc := BounceSeed.singleBounce_coordinates U V north north hseed hreturn
          have hv' : validFrom n 0 0
              ((U ++ north :: north :: V) ++ diagonal :: east :: W) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            firstBounce_word H U V W hallowed hv' hc.1 hc.2
      | @descend A V₀ V₁ U _ _ hV₁ hreturn child =>
          have hA : A = U ++ north :: north :: V₀ := by
            apply List.append_cancel_right (bs := [diagonal])
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using child.word_eq
          have hchildSeed := (BounceSeed.dd_child A V₁ hseed hreturn).1
          have hsplit : validFrom n 0 0
              ((A ++ [diagonal]) ++ diagonal :: (V₁ ++ diagonal :: east :: W)) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          have hNE : validFrom n 0 0
              ((A ++ diagonal :: north :: east :: V₁) ++ diagonal :: east :: W) =
              true := by
            simpa only [SchroderPath.resolveNorthEast_steps, List.append_assoc,
              List.cons_append, List.nil_append] using
              (SchroderPath.resolveNorthEast _ _ hsplit).valid
          have hEN : validFrom n 0 0
              (A ++ diagonal :: east :: north :: (V₁ ++ diagonal :: east :: W)) =
              true := by
            simpa only [SchroderPath.resolveEastNorth_steps, List.append_assoc,
              List.cons_append, List.nil_append] using
              (SchroderPath.resolveEastNorth _ _ hsplit).valid
          have hc := hseed.dd_leading_second_coordinates hreturn
          have hRaisedValid : validFrom n 0 0
              ((A ++ north :: [diagonal]) ++ east :: (V₁ ++ east :: diagonal :: W)) =
              true := by
            simpa only [SchroderPath.secondBounceSuccessor_steps, List.append_assoc,
              List.cons_append, List.nil_append] using
              (SchroderPath.secondBounceSuccessor A (east :: V₁) W hNE hc.2).valid
          have hOrdValid : validFrom n 0 0
              ((A ++ [diagonal]) ++ east :: (north :: (V₁ ++ diagonal :: east :: W))) =
              true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hEN
          have hOrdIH := ih _
            (by simpa only [hlen] using BounceSeed.dd_length_lt (A := A) (V := V₁))
            (A ++ [diagonal]) rfl U V₀ (north :: (V₁ ++ diagonal :: east :: W))
            hchildSeed child hOrdValid
          have hRaisedIH := ih _
            (by simpa only [hlen] using BounceSeed.raise_length_lt (A := A) (V := V₁))
            (A ++ north :: [diagonal]) rfl U (V₀ ++ [north]) (V₁ ++ east :: diagonal :: W)
            hchildSeed.raiseFinal child.raiseFinal hRaisedValid
          have hOrdOut : validFrom n 0 0
              (A ++ east :: diagonal :: north :: (V₁ ++ diagonal :: east :: W)) =
              true := hchildSeed.valid_swapLast hEN
          have hrootSeed : BounceSeed ((A ++ diagonal :: diagonal :: V₁) ++ [diagonal]) := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hseed
          have hrootValid : validFrom n 0 0
              ((A ++ diagonal :: diagonal :: V₁) ++ diagonal :: east :: W) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          have hTarget := hrootSeed.valid_swapLast hrootValid
          have hRaisedEq :
              SchroderPath.evalWord F n
                  (A ++ north :: diagonal :: east :: (V₁ ++ east :: diagonal :: W)) =
                q * SchroderPath.evalWord F n
                  (A ++ north :: east :: diagonal :: (V₁ ++ east :: diagonal :: W)) +
                0 * SchroderPath.evalWord F n
                  (A ++ north :: east :: diagonal :: (V₁ ++ east :: diagonal :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.nil_append, zero_mul,
              add_zero] using hRaisedIH
          have hOrdEq :
              SchroderPath.evalWord F n
                  (A ++ diagonal :: east :: north :: (V₁ ++ diagonal :: east :: W)) =
                q * SchroderPath.evalWord F n
                  (A ++ east :: diagonal :: north :: (V₁ ++ diagonal :: east :: W)) +
                0 * SchroderPath.evalWord F n
                  (A ++ east :: diagonal :: north :: (V₁ ++ diagonal :: east :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, zero_mul, add_zero,
              List.nil_append] using hOrdIH
          have hstep := H.dd_step hq A A A V₁ W q 0 hseed hreturn
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hrootValid)
            rfl rfl hOrdOut hOrdOut
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTarget)
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTarget)
            hRaisedEq hOrdEq
          simpa only [hA, List.append_assoc, List.cons_append, zero_mul, add_zero,
            List.nil_append] using hstep

/-- The generalized NN bounce with a valid successor and strict first-east decrease. -/
theorem generalizedFirstBounce {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V north north)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) :
    ∃ Q : SchroderPath n,
      Q.steps = (U ++ north :: north :: V) ++ east :: diagonal :: W ∧
      F n ⟨Y ++ east :: W, hv⟩ = q * F n Q ∧
      eastCount Q.steps = eastCount (Y ++ east :: W) ∧
      firstEastHeight Q.steps < firstEastHeight (Y ++ east :: W) := by
  have hY : Y = (U ++ north :: north :: V) ++ [diagonal] := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hd.word_eq
  have hs : BounceSeed ((U ++ north :: north :: V) ++ [diagonal]) := hY ▸ hseed
  have hp : validFrom n 0 0
      ((U ++ north :: north :: V) ++ diagonal :: east :: W) = true := by
    simpa only [hY, List.append_assoc, List.cons_append, List.nil_append] using hv
  let Q := SchroderPath.swapDiagonalEast (U ++ north :: north :: V) W hp hs.final_gap
  refine ⟨Q, rfl, ?_, ?_, ?_⟩
  · have hg := H.generalizedFirstBounce_word hq hseed hd hv
    rw [SchroderPath.evalWord_of_valid F n _ hv] at hg
    have hQ : SchroderPath.evalWord F n
        ((U ++ north :: north :: V) ++ east :: diagonal :: W) = F n Q :=
      SchroderPath.evalWord_steps F Q
    rw [hQ] at hg
    exact hg
  · simpa only [Q, SchroderPath.swapDiagonalEast_steps, hY, List.append_assoc,
    List.cons_append, List.nil_append] using
      (eastCount_diagonalEast_swap (U ++ north :: north :: V) W).symm
  · have hno : east ∉ U ++ north :: north :: V := by
      intro he
      exact hs.noEast (List.mem_append_left _ he)
    have hm := firstEastHeight_diagonalEast_swap (U ++ north :: north :: V) W hno
    have hheight : firstEastHeight (Y ++ east :: W) = firstEastHeight Q.steps + 1 := by
      simpa only [Q, SchroderPath.swapDiagonalEast_steps, hY, List.append_assoc,
        List.cons_append, List.nil_append] using hm
    rw [hheight]
    exact Nat.lt_succ_self _

end SatisfiesReductionRecursion

end VerticalStripLLT

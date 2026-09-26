import VerticalStripLLT.GeneralizedBounceDD
import VerticalStripLLT.WordThirdBounce

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- The ND generalized bounce, proved by strong induction on the east-free prefix. -/
theorem generalizedThirdBounce_word {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V north diagonal)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) :
    SchroderPath.evalWord F n (Y ++ east :: W) =
      (q - 1) * SchroderPath.evalWord F n
          ((U ++ north :: diagonal :: V) ++ east :: diagonal :: W) +
        q * SchroderPath.evalWord F n
          ((U ++ diagonal :: north :: V) ++ east :: diagonal :: W) := by
  suffices ∀ k (Z : List Step), Z.length = k →
      ∀ {n : ℕ} (U V W : List Step), BounceSeed Z →
        BounceDecomposition Z U V north diagonal →
        validFrom n 0 0 (Z ++ east :: W) = true →
        SchroderPath.evalWord F n (Z ++ east :: W) =
          (q - 1) * SchroderPath.evalWord F n
              ((U ++ north :: diagonal :: V) ++ east :: diagonal :: W) +
            q * SchroderPath.evalWord F n
              ((U ++ diagonal :: north :: V) ++ east :: diagonal :: W) from
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
          have hc := BounceSeed.singleBounce_coordinates U V north diagonal hseed hreturn
          have hv' : validFrom n 0 0
              ((U ++ north :: diagonal :: V) ++ diagonal :: east :: W) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            thirdBounce_word H hq U V W hallowed hv' hc.1 hc.2
      | @descend A V₀ V₁ U _ _ hV₁ hreturn child =>
          have hA : A = U ++ north :: diagonal :: V₀ := by
            apply List.append_cancel_right (bs := [diagonal])
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using child.word_eq
          have hC : endpointFrom 0 0 (U ++ diagonal :: north :: V₀) =
              endpointFrom 0 0 A := by
            rw [hA]
            exact endpointFrom_diagonalNorth_swap 0 0 U V₀
          have hchildSeed := (BounceSeed.dd_child A V₁ hseed hreturn).1
          have hsplit : validFrom n 0 0
              ((A ++ [diagonal]) ++ diagonal :: (V₁ ++ diagonal :: east :: W)) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          have hNE : validFrom n 0 0
              ((A ++ diagonal :: north :: east :: V₁) ++ diagonal :: east :: W) = true := by
            simpa only [SchroderPath.resolveNorthEast_steps, List.append_assoc,
              List.cons_append, List.nil_append] using
              (SchroderPath.resolveNorthEast _ _ hsplit).valid
          have hEN : validFrom n 0 0
              (A ++ diagonal :: east :: north :: (V₁ ++ diagonal :: east :: W)) = true := by
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
          have hOrdB : validFrom n 0 0
              (A ++ east :: diagonal :: north :: (V₁ ++ diagonal :: east :: W)) = true :=
            hchildSeed.valid_swapLast hEN
          have hOrdC : validFrom n 0 0
              ((U ++ diagonal :: north :: V₀) ++ east :: diagonal :: north ::
                (V₁ ++ diagonal :: east :: W)) = true := by
            have hDN : validFrom n 0 0
                ((U ++ north :: diagonal :: V₀) ++ diagonal :: east ::
                  (north :: (V₁ ++ diagonal :: east :: W))) = true := by
              simpa only [hA, List.append_assoc, List.cons_append, List.nil_append]
                using hOrdValid
            have h := child.valid_nd_successor hchildSeed hDN
            simpa only [List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using h
          have hrootSeed : BounceSeed ((A ++ diagonal :: diagonal :: V₁) ++ [diagonal]) := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hseed
          have hrootValid : validFrom n 0 0
              ((A ++ diagonal :: diagonal :: V₁) ++ diagonal :: east :: W) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          have hTargetB : validFrom n 0 0
              (A ++ diagonal :: diagonal :: (V₁ ++ east :: diagonal :: W)) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using
              hrootSeed.valid_swapLast hrootValid
          have hrootND : validFrom n 0 0
              ((U ++ north :: diagonal :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                diagonal :: east :: W) = true := by
            simpa only [hA, List.append_assoc, List.cons_append, List.nil_append] using hv
          have hTargetC : validFrom n 0 0
              ((U ++ diagonal :: north :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                east :: diagonal :: W) = true := by
            have hrootD : BounceDecomposition
                ((U ++ north :: diagonal :: (V₀ ++ diagonal :: diagonal :: V₁)) ++ [diagonal])
                U (V₀ ++ diagonal :: diagonal :: V₁) north diagonal := by
              have h := BounceDecomposition.descend hV₁ hreturn child
              simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
                List.nil_append] using h
            have hrootSeedND : BounceSeed
                ((U ++ north :: diagonal :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                  [diagonal]) := by
              simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
                List.nil_append] using hseed
            exact hrootD.valid_nd_successor hrootSeedND hrootND
          have hRaisedEq :
              SchroderPath.evalWord F n
                  (A ++ north :: diagonal :: east :: (V₁ ++ east :: diagonal :: W)) =
                (q - 1) * SchroderPath.evalWord F n
                  (A ++ north :: east :: diagonal :: (V₁ ++ east :: diagonal :: W)) +
                  q * SchroderPath.evalWord F n
                  ((U ++ diagonal :: north :: V₀) ++ north :: east :: diagonal ::
                    (V₁ ++ east :: diagonal :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using hRaisedIH
          have hOrdEq :
              SchroderPath.evalWord F n
                  (A ++ diagonal :: east :: north :: (V₁ ++ diagonal :: east :: W)) =
                (q - 1) * SchroderPath.evalWord F n
                  (A ++ east :: diagonal :: north :: (V₁ ++ diagonal :: east :: W)) +
                  q * SchroderPath.evalWord F n
                  ((U ++ diagonal :: north :: V₀) ++ east :: diagonal :: north ::
                    (V₁ ++ diagonal :: east :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using hOrdIH
          have hstep := H.dd_step hq A A (U ++ diagonal :: north :: V₀) V₁ W
            (q - 1) q hseed hreturn
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hrootValid)
            rfl hC hOrdB hOrdC
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTargetB)
            (by
              simpa only [hA, List.append_assoc, List.cons_append, List.nil_append] using
                hTargetC)
            hRaisedEq hOrdEq
          simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
            List.nil_append] using hstep

end SatisfiesReductionRecursion

end VerticalStripLLT

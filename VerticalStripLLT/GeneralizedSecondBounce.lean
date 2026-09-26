import VerticalStripLLT.GeneralizedBounceDD

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- The DN generalized bounce, proved by strong induction on the east-free prefix. -/
theorem generalizedSecondBounce_word {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F) (hq : q - 1 ≠ 0)
    {n : ℕ} {Y U V W : List Step} (hseed : BounceSeed Y)
    (hd : BounceDecomposition Y U V diagonal north)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) :
    SchroderPath.evalWord F n (Y ++ east :: W) =
      SchroderPath.evalWord F n
        ((U ++ north :: diagonal :: V) ++ east :: diagonal :: W) := by
  suffices ∀ k (Z : List Step), Z.length = k →
      ∀ {n : ℕ} (U V W : List Step), BounceSeed Z →
        BounceDecomposition Z U V diagonal north →
        validFrom n 0 0 (Z ++ east :: W) = true →
        SchroderPath.evalWord F n (Z ++ east :: W) =
          SchroderPath.evalWord F n
            ((U ++ north :: diagonal :: V) ++ east :: diagonal :: W) from
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
          have hc := BounceSeed.singleBounce_coordinates U V diagonal north hseed hreturn
          have hv' : validFrom n 0 0
              ((U ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            secondBounce_word H U V W hallowed hv' hc.1 hc.2
      | @descend A V₀ V₁ U _ _ hV₁ hreturn child =>
          have hA : A = U ++ diagonal :: north :: V₀ := by
            apply List.append_cancel_right (bs := [diagonal])
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using child.word_eq
          have hB : endpointFrom 0 0 (U ++ north :: diagonal :: V₀) =
              endpointFrom 0 0 A := by
            rw [hA]
            exact (endpointFrom_diagonalNorth_swap 0 0 U V₀).symm
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
          have hchildDNSeed : BounceSeed
              ((U ++ diagonal :: north :: V₀) ++ [diagonal]) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using hchildSeed
          have hOrdDN : validFrom n 0 0
              ((U ++ diagonal :: north :: V₀) ++ diagonal :: east ::
                (north :: (V₁ ++ diagonal :: east :: W))) = true := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using hOrdValid
          have hOrdOut : validFrom n 0 0
              ((U ++ north :: diagonal :: V₀) ++ east :: diagonal :: north ::
                (V₁ ++ diagonal :: east :: W)) = true := by
            have h := hchildDNSeed.valid_dn_successor hOrdDN
            simpa only [List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using h
          have hrootDN : validFrom n 0 0
              ((U ++ diagonal :: north :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                diagonal :: east :: W) = true := by
            simpa only [hA, List.append_assoc, List.cons_append, List.nil_append] using hv
          have hrootSeed : BounceSeed
              ((U ++ diagonal :: north :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                [diagonal]) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using hseed
          have hTarget : validFrom n 0 0
              ((U ++ north :: diagonal :: (V₀ ++ diagonal :: diagonal :: V₁)) ++
                east :: diagonal :: W) = true :=
            hrootSeed.valid_dn_successor hrootDN
          have hRaisedEq :
              SchroderPath.evalWord F n
                  (A ++ north :: diagonal :: east :: (V₁ ++ east :: diagonal :: W)) =
                (1 : K) * SchroderPath.evalWord F n
                  ((U ++ north :: diagonal :: V₀) ++ north :: east :: diagonal ::
                    (V₁ ++ east :: diagonal :: W)) +
                  0 * SchroderPath.evalWord F n
                  ((U ++ north :: diagonal :: V₀) ++ north :: east :: diagonal ::
                    (V₁ ++ east :: diagonal :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append, one_mul, zero_mul, add_zero] using hRaisedIH
          have hOrdEq :
              SchroderPath.evalWord F n
                  (A ++ diagonal :: east :: north :: (V₁ ++ diagonal :: east :: W)) =
                (1 : K) * SchroderPath.evalWord F n
                  ((U ++ north :: diagonal :: V₀) ++ east :: diagonal :: north ::
                    (V₁ ++ diagonal :: east :: W)) +
                  0 * SchroderPath.evalWord F n
                  ((U ++ north :: diagonal :: V₀) ++ east :: diagonal :: north ::
                    (V₁ ++ diagonal :: east :: W)) := by
            simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append, one_mul, zero_mul, add_zero] using hOrdIH
          have hstep := H.dd_step hq A (U ++ north :: diagonal :: V₀)
            (U ++ north :: diagonal :: V₀) V₁ W 1 0 hseed hreturn
            (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv)
            hB hB hOrdOut hOrdOut
            (by simpa only [hA, List.append_assoc, List.cons_append, List.nil_append] using hTarget)
            (by simpa only [hA, List.append_assoc, List.cons_append, List.nil_append] using hTarget)
            hRaisedEq hOrdEq
          simpa only [hA, List.append_assoc, List.cons_append, List.singleton_append,
            List.nil_append, one_mul, zero_mul, add_zero] using hstep

end SatisfiesReductionRecursion

end VerticalStripLLT

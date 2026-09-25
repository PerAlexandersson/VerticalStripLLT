import VerticalStripLLT.ReductionRecursion
import VerticalStripLLT.ThirdBouncePath
import VerticalStripLLT.ProductReduction
import Mathlib.Tactic.LinearCombination

namespace VerticalStripLLT

namespace SatisfiesReductionRecursion

/-- The additional one-leading-east first bounce, together with the restricted
single-bounce clauses, gives the restricted `north, diagonal` bounce relation. -/
theorem thirdBounce {A : Type*} [CommRing A] [IsDomain A] {q : A} {e : ℕ → A}
    {F : ∀ n, SchroderPath n → A} (hF : SatisfiesReductionRecursion q e F)
    (hq : q - 1 ≠ 0) {n : ℕ} (U V W : List Step)
    (hV : ∀ s ∈ V, s = Step.north ∨ s = Step.diagonal)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.diagonal :: V) ++ Step.diagonal :: Step.east :: W) = true)
    (hreturn : (Step.endpointFrom 0 0 U).2 =
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.diagonal :: V)).1)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.north :: Step.diagonal :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.diagonal :: V)).2) :
    ∃ Q R : SchroderPath n,
      Q.steps = (U ++ Step.north :: Step.diagonal :: V) ++ Step.east :: Step.diagonal :: W ∧
      R.steps = (U ++ Step.diagonal :: Step.north :: V) ++ Step.east :: Step.diagonal :: W ∧
      F n ⟨(U ++ Step.north :: Step.diagonal :: V) ++ Step.diagonal :: Step.east :: W, h⟩ =
        (q - 1) * F n Q + q * F n R := by
  open Step SchroderPath in
  obtain ⟨hE_dn, hE_nne, hE_enn, hE_e⟩ := endpointFrom_thirdBounce_blocks U V
  have hai := thirdBounce_corner_lt U V hreturn
  have hP' : validFrom n 0 0 ((U ++ diagonal :: north :: V) ++ diagonal :: east :: W) =
      true := by
    have h₁ : validFrom n 0 0 (U ++ north :: diagonal :: (V ++ diagonal :: east :: W)) =
        true := by
      simpa only [List.append_assoc, List.cons_append] using h
    simpa only [List.append_assoc, List.cons_append] using
      validFrom_northDiagonal_swap n 0 0 h₁ hai
  have hgap' : (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).2 := by
    rw [hE_dn]
    exact hgap
  let Q : SchroderPath n := swapDiagonalEast (U ++ north :: diagonal :: V) W h hgap
  let R : SchroderPath n := swapDiagonalEast (U ++ diagonal :: north :: V) W hP' hgap'
  refine ⟨Q, R, rfl, rfl, ?_⟩
  have hPu : validFrom n 0 0 ((U ++ [north]) ++ diagonal :: (V ++ diagonal :: east :: W)) =
      true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using h
  have hQu : validFrom n 0 0 ((U ++ [north]) ++ diagonal :: (V ++ east :: diagonal :: W)) =
      true := by
    simpa only [Q, swapDiagonalEast_steps, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using Q.valid
  have hRu : validFrom n 0 0 (U ++ diagonal :: (north :: V ++ east :: diagonal :: W)) =
      true := by
    simpa only [R, swapDiagonalEast_steps, List.append_assoc, List.cons_append,
      List.nil_append] using R.valid
  have hP'u : validFrom n 0 0 (U ++ diagonal :: (north :: V ++ diagonal :: east :: W)) =
      true := by
    simpa only [List.append_assoc, List.cons_append] using hP'
  have u1 := hF.toSatisfiesRecursion.unicellular _ _ hPu
  have u2 := hF.toSatisfiesRecursion.unicellular _ _ hQu
  have u3 := hF.toSatisfiesRecursion.unicellular _ _ hRu
  have u4 := hF.toSatisfiesRecursion.unicellular _ _ hP'u
  have hf1 : validFrom n 0 0 ((U ++ north :: north :: east :: V) ++ diagonal :: east :: W) =
      true := by
    simpa only [resolveNorthEast_steps, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using (resolveNorthEast _ _ hPu).valid
  have hret1 : (endpointFrom 0 0 U).2 =
      (endpointFrom 0 0 (U ++ north :: north :: east :: V)).1 := by
    rw [hE_nne]
    exact hreturn
  have hgap1 : (endpointFrom 0 0 (U ++ north :: north :: east :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ north :: north :: east :: V)).2 := by
    rw [hE_nne]
    exact hgap
  have f1 := hF.firstBounceOneLeadingEast U V W hV hf1 hret1 hgap1
  have hf2 : validFrom n 0 0 (((U ++ [east]) ++ north :: north :: V) ++ diagonal :: east :: W) =
      true := by
    simpa only [resolveEastNorth_steps, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using (resolveEastNorth _ _ hP'u).valid
  have hret2 : (endpointFrom 0 0 (U ++ [east])).2 =
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 := by
    rw [hE_enn, hE_e]
    exact hreturn
  have hgap2 : (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 + 1 <
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).2 := by
    rw [hE_enn]
    exact hgap
  have f2 := hF.toSatisfiesRecursion.firstBounce (U ++ [east]) V W hV hf2 hret2 hgap2
  have hret3 : (endpointFrom 0 0 U).2 =
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 := by
    rw [hE_dn]
    exact hreturn
  have s := hF.toSatisfiesRecursion.secondBounce U V W hV hP' hret3 hgap'
  rw [SchroderPath.invariant_congr F (⟨_, hPu⟩ : SchroderPath n) ⟨_, h⟩ rfl ?_] at u1
  rw [SchroderPath.invariant_congr F (⟨_, hQu⟩ : SchroderPath n) Q rfl ?_] at u2
  rw [SchroderPath.invariant_congr F (⟨_, hRu⟩ : SchroderPath n) R rfl ?_,
    SchroderPath.invariant_congr F (resolveNorthEast _ _ hRu) (resolveEastNorth _ _ hQu)
      rfl ?_] at u3
  rw [SchroderPath.invariant_congr F (resolveNorthEast _ _ hP'u) (resolveEastNorth _ _ hPu)
    rfl ?_] at u4
  rw [SchroderPath.invariant_congr F (⟨_, hf1⟩ : SchroderPath n)
      (resolveNorthEast _ _ hPu) rfl ?_,
    SchroderPath.invariant_congr F (swapDiagonalEast _ W hf1 hgap1)
      (resolveNorthEast _ _ hQu) rfl ?_] at f1
  rw [SchroderPath.invariant_congr F (⟨_, hf2⟩ : SchroderPath n)
      (resolveEastNorth _ _ hP'u) rfl ?_,
    SchroderPath.invariant_congr F (swapDiagonalEast _ W hf2 hgap2)
      (resolveEastNorth _ _ hRu) rfl ?_] at f2
  rw [SchroderPath.invariant_congr F (⟨_, hP'⟩ : SchroderPath n) ⟨_, hP'u⟩ rfl ?_,
    SchroderPath.invariant_congr F (secondBounceSuccessor U V W hP' hgap') Q rfl ?_] at s
  apply mul_left_cancel₀ hq
  linear_combination (-1 : A) * u1 + f1 - u4 - f2 - (q - 1) * s + q * u2 + q * u3
  all_goals simp [Q, R]

end SatisfiesReductionRecursion

end VerticalStripLLT

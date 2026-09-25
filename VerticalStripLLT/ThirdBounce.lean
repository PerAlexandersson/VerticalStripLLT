import VerticalStripLLT.ThirdBouncePath
import VerticalStripLLT.ThirdBounceWeight
import VerticalStripLLT.FirstBounce
import VerticalStripLLT.SecondBounce
import VerticalStripLLT.Unicellular
import VerticalStripLLT.PolynomialCancellation
import Mathlib.Tactic.LinearCombination

namespace VerticalStripLLT

theorem coloringLLT_thirdBounce {n : ℕ} (U V W : List Step)
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
      ∀ m : ℕ,
        coloringLLT
          (⟨(U ++ Step.north :: Step.diagonal :: V) ++ Step.diagonal :: Step.east :: W, h⟩ :
            SchroderPath n) m =
          MvPolynomial.C (Polynomial.X - 1) * coloringLLT Q m +
            MvPolynomial.C Polynomial.X * coloringLLT R m := by
  open Step SchroderPath in
  -- Endpoint facts: `U` ends at `(a,i)` with `a < i`; all block variants share the
  -- endpoint `(i,j)` of `U n d V`.
  obtain ⟨hE_dn, hE_nne, hE_enn, hE_e⟩ := endpointFrom_thirdBounce_blocks U V
  have hai := thirdBounce_corner_lt U V hreturn
  -- The valid path `P' = U d n V d e W` (the second-bounce source).
  have hP' : validFrom n 0 0 ((U ++ diagonal :: north :: V) ++ diagonal :: east :: W) = true := by
    have h₁ : validFrom n 0 0 (U ++ north :: diagonal :: (V ++ diagonal :: east :: W)) = true := by
      simpa only [List.append_assoc, List.cons_append] using h
    simpa only [List.append_assoc, List.cons_append] using
      validFrom_northDiagonal_swap n 0 0 h₁ hai
  have hgap' : (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ diagonal :: north :: V)).2 := by
    rw [hE_dn]; exact hgap
  let Q : SchroderPath n := swapDiagonalEast (U ++ north :: diagonal :: V) W h hgap
  let R : SchroderPath n := swapDiagonalEast (U ++ diagonal :: north :: V) W hP' hgap'
  refine ⟨Q, R, rfl, rfl, fun m => ?_⟩
  -- Unicellular identities.
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
  have u1 := coloringLLT_unicellular _ _ hPu m
  have u2 := coloringLLT_unicellular _ _ hQu m
  have u3 := coloringLLT_unicellular _ _ hRu m
  have u4 := coloringLLT_unicellular _ _ hP'u m
  -- First-bounce identities.
  have hf1 : validFrom n 0 0 ((U ++ north :: north :: east :: V) ++ diagonal :: east :: W) =
      true := by
    simpa only [resolveNorthEast_steps, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using (resolveNorthEast _ _ hPu).valid
  have hret1 : (endpointFrom 0 0 U).2 =
      (endpointFrom 0 0 (U ++ north :: north :: east :: V)).1 := by
    rw [hE_nne]; exact hreturn
  have hgap1 : (endpointFrom 0 0 (U ++ north :: north :: east :: V)).1 + 1 <
      (endpointFrom 0 0 (U ++ north :: north :: east :: V)).2 := by
    rw [hE_nne]; exact hgap
  have f1 := coloringLLT_firstBounce_general U (east :: V) W hf1 hret1 hgap1 m
  have hf2 : validFrom n 0 0 (((U ++ [east]) ++ north :: north :: V) ++ diagonal :: east :: W) =
      true := by
    simpa only [resolveEastNorth_steps, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using (resolveEastNorth _ _ hP'u).valid
  have hret2 : (endpointFrom 0 0 (U ++ [east])).2 =
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 := by
    rw [hE_enn, hE_e]; exact hreturn
  have hgap2 : (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).1 + 1 <
      (endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V)).2 := by
    rw [hE_enn]; exact hgap
  have f2 := coloringLLT_firstBounce (U ++ [east]) V W hV hf2 hret2 hgap2 m
  -- Second-bounce identity.
  have hret3 : (endpointFrom 0 0 U).2 = (endpointFrom 0 0 (U ++ diagonal :: north :: V)).1 := by
    rw [hE_dn]; exact hreturn
  have s := coloringLLT_secondBounce U V W hV hP' hret3 hgap' m
  -- Identify all paths through their step words.
  rw [coloringLLT_congr_steps (⟨_, hPu⟩ : SchroderPath n) ⟨_, h⟩ ?_ m] at u1
  rw [coloringLLT_congr_steps (⟨_, hQu⟩ : SchroderPath n) Q ?_ m] at u2
  rw [coloringLLT_congr_steps (⟨_, hRu⟩ : SchroderPath n) R ?_ m,
    coloringLLT_congr_steps (resolveNorthEast _ _ hRu) (resolveEastNorth _ _ hQu) ?_ m] at u3
  rw [coloringLLT_congr_steps (resolveNorthEast _ _ hP'u) (resolveEastNorth _ _ hPu) ?_ m] at u4
  rw [coloringLLT_congr_steps (⟨_, hf1⟩ : SchroderPath n) (resolveNorthEast _ _ hPu) ?_ m,
    coloringLLT_congr_steps (swapDiagonalEast _ W hf1 hgap1) (resolveNorthEast _ _ hQu)
      ?_ m] at f1
  rw [coloringLLT_congr_steps (⟨_, hf2⟩ : SchroderPath n) (resolveEastNorth _ _ hP'u) ?_ m,
    coloringLLT_congr_steps (swapDiagonalEast _ W hf2 hgap2) (resolveEastNorth _ _ hRu)
      ?_ m] at f2
  rw [coloringLLT_congr_steps (⟨_, hP'⟩ : SchroderPath n) ⟨_, hP'u⟩ ?_ m,
    coloringLLT_congr_steps (secondBounceSuccessor U V W hP' hgap') Q ?_ m] at s
  -- Cancel the nonzero factor `q - 1` and conclude by linear algebra.
  rw [← qSubOne_mul_eq_iff]
  simp only [map_sub, map_one] at u1 u2 u3 u4 ⊢
  linear_combination (-1 : XPoly m) * u1 + f1 - u4 - f2 -
    (MvPolynomial.C Polynomial.X - 1) * s + MvPolynomial.C Polynomial.X * u2 +
    MvPolynomial.C Polynomial.X * u3
  all_goals simp [Q, R]

end VerticalStripLLT

import VerticalStripLLT.CyclicHessenberg.RootDeletion
import VerticalStripLLT.OrientationNatural
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! The natural-coefficient deletion expression.
Its equality with the independent coloring enumerator requires the color-insertion theorem. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- Delete a subset containing the largest vertex and recurse on its complement.
This constructs an elementary expression; it is not the definition of the loop polynomial. -/
noncomputable def naturalKernelExpansion (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) : NEExpansion := by
  classical
  exact if hS : S.Nonempty then
    ∑ U : S.powerset, if hr : S.max' hS ∈ U.val then
      natElementary ⟨U.val.card, Finset.card_pos.mpr ⟨S.max' hS, hr⟩⟩ *
        naturalKernelExpansion (S \ U.val)
          (rootDeletion Polynomial.X Z U.val (S.max' hS))
    else 0
  else MvPolynomial.C (Z [] [])
termination_by S.card
decreasing_by
  have hsub : U.val ⊆ S := Finset.mem_powerset.mp U.property
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hpos := Finset.card_pos.mpr ⟨S.max' hS, hr⟩
  lia

/-- Cast the constructed natural expression to the existing elementary algebra. -/
noncomputable def kernelExpansion (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) : EExpansion :=
  naturalCast (naturalKernelExpansion S Z)

@[simp] theorem naturalKernelExpansion_empty (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion ∅ Z = MvPolynomial.C (Z [] []) := by
  rw [naturalKernelExpansion]
  simp

/-- The defining positive root recurrence, with its strict cardinality decrease. -/
theorem naturalKernelExpansion_eq_rootSum (S : Finset V)
    (hS : S.Nonempty) (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion S Z =
      ∑ U : S.powerset, if hr : S.max' hS ∈ U.val then
        natElementary ⟨U.val.card, Finset.card_pos.mpr ⟨S.max' hS, hr⟩⟩ *
          naturalKernelExpansion (S \ U.val)
            (rootDeletion Polynomial.X Z U.val (S.max' hS))
      else 0 := by
  classical
  rw [naturalKernelExpansion, dif_pos hS]

/-- The deletion expression is additive in the original kernel. -/
theorem naturalKernelExpansion_add (S : Finset V)
    (Z W : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion S (fun l t => Z l t + W l t) =
      naturalKernelExpansion S Z + naturalKernelExpansion S W := by
  classical
  induction S using Finset.strongInductionOn generalizing Z W with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · simp only [naturalKernelExpansion_eq_rootSum S hS, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hr : S.max' hS ∈ U.val
      · simp only [dif_pos hr, rootDeletion_add]
        rw [ih (S \ U.val) (Finset.sdiff_ssubset
          (Finset.mem_powerset.mp U.property) ⟨S.max' hS, hr⟩), mul_add]
      · simp only [dif_neg hr, add_zero]
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp

/-- Scalar linearity is needed when the root recurrence is unrolled into cycles. -/
theorem naturalKernelExpansion_smul (S : Finset V) (a : Polynomial ℕ)
    (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion S (fun l t => a * Z l t) =
      MvPolynomial.C a * naturalKernelExpansion S Z := by
  classical
  induction S using Finset.strongInductionOn generalizing Z with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · simp only [naturalKernelExpansion_eq_rootSum S hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hr : S.max' hS ∈ U.val
      · simp only [dif_pos hr, rootDeletion_smul]
        rw [ih (S \ U.val) (Finset.sdiff_ssubset
          (Finset.mem_powerset.mp U.property) ⟨S.max' hS, hr⟩)]
        ring
      · simp only [dif_neg hr, mul_zero]
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp

@[simp] theorem naturalKernelExpansion_zero (S : Finset V) :
    naturalKernelExpansion S (fun _ _ => 0) = 0 := by
  simpa using naturalKernelExpansion_smul S 0 (fun _ _ => 0)

/-- Every coefficient of the constructed expression is the image of a natural coefficient.
The semantic identification with the coloring sum is a separate obligation. -/
theorem kernelExpansion_coeff_nonneg (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((kernelExpansion S Z).coeff d).coeff j := by
  simp only [kernelExpansion, naturalCast, MvPolynomial.coeff_map,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact Nat.cast_nonneg _

end VerticalStripLLT.CyclicHessenberg

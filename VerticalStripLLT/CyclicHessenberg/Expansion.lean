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

/-- Every coefficient of the constructed expression is the image of a natural coefficient.
The semantic identification with the coloring sum is a separate obligation. -/
theorem kernelExpansion_coeff_nonneg (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) (d : ℕ+ →₀ ℕ) (j : ℕ) :
    0 ≤ ((kernelExpansion S Z).coeff d).coeff j := by
  simp only [kernelExpansion, naturalCast, MvPolynomial.coeff_map,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact Nat.cast_nonneg _

end VerticalStripLLT.CyclicHessenberg

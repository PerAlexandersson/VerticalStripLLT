import VerticalStripLLT.CyclicHessenberg.Expansion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option autoImplicit false

/-! The deletion expansion is homogeneous in its elementary generators. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The natural deletion expansion has weighted degree equal to the support size. -/
theorem naturalKernelExpansion_isWeightedHomogeneous_degree (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
      (naturalKernelExpansion S Z) S.card := by
  classical
  induction S using Finset.strongInductionOn generalizing Z with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · rw [naturalKernelExpansion_eq_rootSum S hS Z]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro U hU
      by_cases hr : S.max' hS ∈ U.val
      · simp only [dite_eq_left hr]
        have hsub : U.val ⊆ S := Finset.mem_powerset.mp U.property
        have hgen :
            MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
              (natElementary
                ⟨U.val.card, Finset.card_pos.mpr ⟨S.max' hS, hr⟩⟩) U.val.card := by
          simpa only [natElementary] using
            (MvPolynomial.isWeightedHomogeneous_X (Polynomial ℕ)
              (fun d : ℕ+ => d.val)
              ⟨U.val.card, Finset.card_pos.mpr ⟨S.max' hS, hr⟩⟩)
        have hres := ih (S \ U.val)
          (Finset.sdiff_ssubset hsub ⟨S.max' hS, hr⟩)
          (rootDeletion Polynomial.X Z U.val (S.max' hS))
        have hdegree : U.val.card + (S \ U.val).card = S.card := by
          have hcard := Finset.card_sdiff_add_card_eq_card hsub
          lia
        simpa only [hdegree] using hgen.mul hres
      · simp only [dite_eq_right hr]
        exact MvPolynomial.isWeightedHomogeneous_zero
          (Polynomial ℕ) (fun d : ℕ+ => d.val) S.card
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simpa only [naturalKernelExpansion_empty, Finset.card_empty] using
        (MvPolynomial.isWeightedHomogeneous_C
          (fun d : ℕ+ => d.val) (Z [] []))

private theorem naturalCast_isWeightedHomogeneous_degree {p : NEExpansion}
    {n : ℕ} (hp : MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val) p n) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val) (naturalCast p) n := by
  intro d hd
  have hcoeff : (naturalCast p).coeff d =
      Polynomial.mapRingHom (Nat.castRingHom ℤ) (p.coeff d) := by
    simp only [naturalCast, MvPolynomial.coeff_map]
  have hsource : p.coeff d ≠ 0 := by
    intro hzero
    have hzeroMap : (naturalCast p).coeff d = 0 := by
      rw [hcoeff, hzero, map_zero]
    exact hd hzeroMap
  exact hp hsource

/-- The existing signed-coefficient kernel expansion has the same weighted degree. -/
theorem kernelExpansion_isWeightedHomogeneous_degree (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
      (kernelExpansion S Z) S.card := by
  change MvPolynomial.IsWeightedHomogeneous (fun d : ℕ+ => d.val)
    (naturalCast (naturalKernelExpansion S Z)) S.card
  exact naturalCast_isWeightedHomogeneous_degree
    (naturalKernelExpansion_isWeightedHomogeneous_degree S Z)

end VerticalStripLLT.CyclicHessenberg

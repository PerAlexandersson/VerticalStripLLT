import VerticalStripLLT.BounceMatching
-- Local helper module: VerticalStripLLT.BounceAssembly

/-! ## Assembly of the first bounce identity -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

theorem orientationExpansionAt_bounce_core {B P T : SchroderPath n} {i y t : Fin n}
    (hy : y.val = i.val + 1) (hyt : y < t) (hiy : (i, y) ∈ B.normalEdges)
    (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y))
    (hfresh : (y, t) ∉ B.normalEdges)
    (hPN : P.normalEdges = insert (y, t) B.normalEdges)
    (hPS : P.strictEdges = insert (i, t) B.strictEdges)
    (hTN : B.normalEdges = T.normalEdges)
    (hTS : T.strictEdges = insert (y, t) B.strictEdges) (z : Q) :
    orientationExpansionAt P z = MvPolynomial.C (z + 1) * orientationExpansionAt T z := by
  classical
  let E := orientationInsertEquiv (y, t) hfresh hPN
  let wT : Orientation B → EExpansion := fun θ =>
    MvPolynomial.C (z ^ orientationAsc B θ) * fiberMono (gh (RT y t θ))
  have hP : orientationExpansionAt P z = ∑ p : Bool × Orientation B,
      MvPolynomial.C (z ^ (orientationAsc B p.2 + if p.1 then 1 else 0)) *
        fiberMono (gh (RP i y t p.1 p.2)) := by
    unfold orientationExpansionAt
    rw [← Equiv.sum_comp E.symm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [orientationAsc_insert, hrvMonomial_eq_fiberMono, hrv_eq_gh,
      gh_congr (upwardStep_source_iff t hfresh hPN hPS p.1 p.2)]
  have hT : orientationExpansionAt T z = ∑ θ : Orientation B, wT θ := by
    rw [← orientationExpansionAt_sum_transport hTN z]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [orientationAsc_transport, hrvMonomial_eq_fiberMono, hrv_eq_gh,
      gh_congr (upwardStep_succ_iff t hTN hTS θ)]
  have hRHS : MvPolynomial.C (z + 1) * ∑ θ : Orientation B, wT θ =
      ∑ q : Bool × Orientation B, MvPolynomial.C (z ^ (if q.1 then 1 else 0)) * wT q.2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [ite_true, pow_one, Bool.false_eq_true, ite_false, pow_zero, MvPolynomial.C_1,
      one_mul, MvPolynomial.C_add]
    ring
  rw [hP, hT, hRHS]
  symm
  rw [← (bounceMatch_bijective hy hyt hiy hSinv hNinv).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨hasc, hmono⟩ := bounceMatch_spec hy hyt hiy hSinv hNinv p
  simp only [wT]
  rw [hasc, ← hmono, pow_add, MvPolynomial.C_mul]
  ring

end BounceHRV
end VerticalStripLLT

namespace VerticalStripLLT


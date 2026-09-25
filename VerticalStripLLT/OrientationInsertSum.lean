import VerticalStripLLT.OrientationInsertStep
import VerticalStripLLT.OrientationTransport
import VerticalStripLLT.HRVCongruence

open scoped BigOperators

namespace VerticalStripLLT

theorem orientationExpansionAt_insert_sum {n : ℕ} {P R : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges) (z : Q) :
    orientationExpansionAt R z =
      ∑ θ : Orientation P,
        (MvPolynomial.C (z ^ orientationAsc R
            ((orientationInsertEquiv a hnot hN).symm (false, θ))) *
            hrvMonomial ((orientationInsertEquiv a hnot hN).symm (false, θ)) +
          MvPolynomial.C (z ^ orientationAsc R
            ((orientationInsertEquiv a hnot hN).symm (true, θ))) *
            hrvMonomial ((orientationInsertEquiv a hnot hN).symm (true, θ))) := by
  unfold orientationExpansionAt
  rw [← Equiv.sum_comp (orientationInsertEquiv a hnot hN).symm,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Fintype.sum_bool, add_comm]

theorem insert_false_summand {n : ℕ} {P R : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges)
    (hS : R.strictEdges = P.strictEdges) (z : Q) (θ : Orientation P) :
    MvPolynomial.C (z ^ orientationAsc R
      ((orientationInsertEquiv a hnot hN).symm (false, θ))) *
        hrvMonomial ((orientationInsertEquiv a hnot hN).symm (false, θ)) =
      MvPolynomial.C (z ^ orientationAsc P θ) * hrvMonomial θ := by
  rw [orientationAsc_insert,
    hrvMonomial_congr_of_upwardStep (η := θ)]
  · simp
  · intro u v
    rw [upwardStep_orientationInsert_iff a hnot hN hS]
    simp

theorem insert_true_summand {n : ℕ} {P R D : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges)
    (hS : R.strictEdges = P.strictEdges)
    (hND : P.normalEdges = D.normalEdges)
    (hSD : D.strictEdges = insert a P.strictEdges) (z : Q)
    (θ : Orientation P) :
    MvPolynomial.C (z ^ orientationAsc R
      ((orientationInsertEquiv a hnot hN).symm (true, θ))) *
        hrvMonomial ((orientationInsertEquiv a hnot hN).symm (true, θ)) =
      MvPolynomial.C z *
        (MvPolynomial.C (z ^ orientationAsc D (orientationTransport hND θ)) *
          hrvMonomial (orientationTransport hND θ)) := by
  rw [orientationAsc_insert, orientationAsc_transport,
    hrvMonomial_congr_of_upwardStep (η := orientationTransport hND θ)]
  · simp only [ite_true, pow_succ, MvPolynomial.C_mul]
    ring
  · intro u v
    rw [upwardStep_orientationInsert_iff a hnot hN hS,
      upwardStep_transport_iff, hSD, Finset.mem_insert]
    unfold upwardStep
    tauto

end VerticalStripLLT

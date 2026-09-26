import VerticalStripLLT.OrientationExpansion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

namespace VerticalStripLLT

open scoped BigOperators

theorem hrvFiber_card_sum {n : ℕ} {P : SchroderPath n}
    (θ : Orientation P) :
    ∑ r : Fin n, (hrvFiber θ r).card = n := by
  classical
  have hcard : (Finset.univ : Finset (Fin n)).card =
      ∑ r ∈ (Finset.univ : Finset (Fin n)),
        ((Finset.univ : Finset (Fin n)).filter (fun u => hrv θ u = r)).card :=
    Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := hrv θ) (by
        intro u hu
        exact Finset.mem_univ _)
  simpa [hrvFiber] using hcard.symm

theorem hrvMonomial_isWeightedHomogeneous_degree {n : ℕ}
    {P : SchroderPath n} (θ : Orientation P) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (hrvMonomial θ) n := by
  classical
  have hp := MvPolynomial.IsWeightedHomogeneous.prod
    (s := (Finset.univ : Finset (Fin n)))
    (φ := fun r => if h : (hrvFiber θ r).Nonempty then
      elementary ⟨(hrvFiber θ r).card, Finset.card_pos.mpr h⟩ else 1)
    (n := fun r => (hrvFiber θ r).card) (w := fun k : ℕ+ => k.val)
      (by
        intro r hr
        split_ifs with h
        · exact MvPolynomial.isWeightedHomogeneous_X Q _ _
        · have he : hrvFiber θ r = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          simpa only [he, Finset.card_empty] using
            MvPolynomial.isWeightedHomogeneous_one Q (fun k : ℕ+ => k.val))
  rw [hrvFiber_card_sum θ] at hp
  exact hp

theorem orientationExpansionAt_isWeightedHomogeneous_degree {n : ℕ}
    {P : SchroderPath n} (z : Q) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (orientationExpansionAt P z) n := by
  unfold orientationExpansionAt
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro θ hθ
  exact (hrvMonomial_isWeightedHomogeneous_degree θ).C_mul
    (z ^ orientationAsc P θ)

theorem orientationExpansion_isWeightedHomogeneous_degree {n : ℕ}
    (P : SchroderPath n) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (orientationExpansion P) n := by
  simpa only [orientationExpansion] using
    orientationExpansionAt_isWeightedHomogeneous_degree
      (P := P) (Polynomial.X - 1)

theorem shiftedOrientationExpansion_isWeightedHomogeneous_degree
    {n : ℕ} (P : SchroderPath n) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (shiftedOrientationExpansion P) n := by
  simpa only [shiftedOrientationExpansion] using
    orientationExpansionAt_isWeightedHomogeneous_degree
      (P := P) Polynomial.X

end VerticalStripLLT

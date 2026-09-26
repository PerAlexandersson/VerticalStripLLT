import VerticalStripLLT.Circular.HRV
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Weighted degree of the circular HRV expansion. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

namespace Orientation

variable {n : ℕ} {D : Diagram n}

theorem hrvFiber_card_sum (θ : Orientation D) :
    ∑ r : Fin n, (Finset.univ.filter (fun u => θ.hrv u = r)).card = n := by
  classical
  have hcard : (Finset.univ : Finset (Fin n)).card =
      ∑ r ∈ (Finset.univ : Finset (Fin n)),
        ((Finset.univ : Finset (Fin n)).filter (fun u => θ.hrv u = r)).card :=
    Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := θ.hrv) (by
        intro u hu
        exact Finset.mem_univ _)
  simpa using hcard.symm

theorem hrvMonomial_isWeightedHomogeneous_degree (θ : Orientation D) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      θ.hrvMonomial n := by
  classical
  have hp := MvPolynomial.IsWeightedHomogeneous.prod
    (s := (Finset.univ : Finset (Fin n)))
    (φ := fun r =>
      if h : 0 < (Finset.univ.filter (fun u => θ.hrv u = r)).card then
        elementary ⟨(Finset.univ.filter (fun u => θ.hrv u = r)).card, h⟩
      else 1)
    (n := fun r => (Finset.univ.filter (fun u => θ.hrv u = r)).card)
    (w := fun k : ℕ+ => k.val)
      (by
        intro r hr
        split_ifs with h
        · exact MvPolynomial.isWeightedHomogeneous_X Q _ _
        · have he : (Finset.univ.filter (fun u => θ.hrv u = r)) = ∅ := by
            exact Finset.card_eq_zero.mp (by lia)
          simpa only [he, Finset.card_empty] using
            MvPolynomial.isWeightedHomogeneous_one Q (fun k : ℕ+ => k.val))
  rw [hrvFiber_card_sum θ] at hp
  exact hp

end Orientation

theorem shiftedOrientationExpansion_isWeightedHomogeneous_degree
    {n : ℕ} (D : Diagram n) :
    MvPolynomial.IsWeightedHomogeneous (fun k : ℕ+ => k.val)
      (shiftedOrientationExpansion D) n := by
  unfold shiftedOrientationExpansion
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro θ hθ
  exact (Orientation.hrvMonomial_isWeightedHomogeneous_degree θ).C_mul
    (Polynomial.X ^ θ.val.card)

end VerticalStripLLT.Circular

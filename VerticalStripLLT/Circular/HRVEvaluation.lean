import VerticalStripLLT.Circular.HRV

/-! Finite-alphabet evaluation of the independently defined circular HRV monomial. -/

namespace VerticalStripLLT.Circular.Orientation

open scoped BigOperators Classical

variable {n : ℕ} {D : Diagram n}

theorem evalElementary_hrvMonomial (θ : Orientation D) (m : ℕ) :
    evalElementary m θ.hrvMonomial =
      ∏ r : Fin n, MvPolynomial.esymm (Fin m) Q
        (Finset.univ.filter fun u => θ.hrv u = r).card := by
  rw [hrvMonomial, map_prod]
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : 0 < (Finset.univ.filter fun u => θ.hrv u = r).card
  · rw [dite_eq_left h]
    exact evalElementary_elementary m _
  · have hz : (Finset.univ.filter fun u => θ.hrv u = r).card = 0 :=
      Nat.eq_zero_of_not_pos h
    simp [hz]

end VerticalStripLLT.Circular.Orientation

import VerticalStripLLT.Components.HRVGainPotential
import VerticalStripLLT.Components.GainPotentialValues

/-! Signed deletion preserves arbitrary values of the entire lifted HRV map. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n} {M : Type*} [AddCommGroup M]

/-- The HRV deletion recurrence holds before any residue or fiber evaluation.
The supplied orientations describe the actual selections `A ∪ J`. -/
theorem sum_powerset_liftedHRV_value_eq_zero
    (A N : Finset (Edge D.area)) (P Nsteps : List (Edge D.area))
    (θ : Finset (Edge D.area) → Orientation D)
    (hθ : ∀ J ⊆ N, (θ J).val = A ∪ J)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hP : ∀ e ∈ P, e ∈ D.strict ∪ A)
    (hperm : (P.map Edge.head ++ Nsteps.map Edge.tail).Perm
      (P.map Edge.tail ++ Nsteps.map Edge.head))
    (hexcess : (Nsteps.map (fun e => (e.length.val : ℤ))).sum <
      (P.map (fun e => (e.length.val : ℤ))).sum)
    (value : (ℤ → ℤ) → M) :
    (∑ J ∈ N.powerset, ((-1 : ℤ) ^ J.card) • value (θ J).liftedHRV) = 0 := by
  let eval (p : Fin n → ℕ) : M := value (fun z => z + (p (D.residue z) : ℤ))
  have hzero := D.reversedGain.sum_powerset_potential_value_eq_zero_of_gain_excess
    (D.strict ∪ A) N P Nsteps eval hN hP hperm.symm hexcess
  have hterm (J : Finset (Edge D.area)) (hJ : J ∈ N.powerset) :
      (if ∃ p, D.reversedGain.Feasible ((D.strict ∪ A) ∪ J) p
       then ((-1 : ℤ) ^ J.card) • eval (D.reversedGain.potential ((D.strict ∪ A) ∪ J))
       else 0) = ((-1 : ℤ) ^ J.card) • value (θ J).liftedHRV := by
    have hset : (D.strict ∪ A) ∪ J = D.strict ∪ (θ J).val := by
      rw [hθ J (Finset.mem_powerset.mp hJ), Finset.union_assoc]
    have hfeas : ∃ p, D.reversedGain.Feasible ((D.strict ∪ A) ∪ J) p := by
      rw [hset]
      exact ⟨(θ J).hrvDistance, (θ J).hrvDistance_feasible⟩
    rw [ite_eq_left hfeas]
    have hmap : (fun z => z +
        (D.reversedGain.potential ((D.strict ∪ A) ∪ J) (D.residue z) : ℤ)) =
        (θ J).liftedHRV := by
      funext z
      rw [hset, (θ J).liftedHRV_eq_add_potential]
    rw [show eval (D.reversedGain.potential ((D.strict ∪ A) ∪ J)) =
      value (θ J).liftedHRV from congrArg value hmap]
  rw [Finset.sum_congr rfl hterm] at hzero
  exact hzero

end

end VerticalStripLLT.Circular

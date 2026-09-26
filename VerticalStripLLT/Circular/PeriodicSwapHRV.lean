import VerticalStripLLT.Circular.PeriodicSwap
import VerticalStripLLT.Circular.PeriodicSwapResidue
import VerticalStripLLT.Circular.HRVConjugacy

/-! The sink-order condition for a periodic adjacent swap with a selected outgoing edge. -/

namespace VerticalStripLLT.Circular

def periodicSwapEquiv (n p : ℤ) (hn : 2 ≤ n) : ℤ ≃ ℤ :=
  Function.Involutive.toPerm (periodicSwap n p) (periodicSwap_involutive n p hn)

namespace Orientation

variable {n : ℕ} {D D' : Diagram n}

/-- A selected outgoing edge at the first swapped lift prevents the swapped pair being sinks. -/
theorem periodicSwap_sink_order (θ : Orientation D) (p : ℤ) (hn : 2 ≤ (n : ℤ))
    (hout : ∃ w, D.liftStep θ.val p w) :
    ∀ x y, (∀ z, ¬ D.liftStep θ.val x z) →
      (∀ z, ¬ D.liftStep θ.val y z) → x ≤ y →
      periodicSwap n p x ≤ periodicSwap n p y := by
  let S : Set ℤ := {x | ∀ z, ¬ D.liftStep θ.val x z}
  have hS : ∀ k : ℤ, ¬ (p + (n : ℤ) * k ∈ S ∧ p + 1 + (n : ℤ) * k ∈ S) := by
    intro k h
    obtain ⟨w, hw⟩ := hout
    exact h.1 (w + (n : ℤ) * k) ((D.liftStep_translate_iff p w k).mpr hw)
  have hmono := periodicSwap_strictMonoOn n p hn S hS
  intro x y hx hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hmono hx hy hlt).le

theorem liftedHRV_periodicSwap (θ : Orientation D) (η : Orientation D')
    (p : ℤ) (hn : 2 ≤ (n : ℤ)) (hout : ∃ w, D.liftStep θ.val p w)
    (hstep : ∀ x y, D.liftStep θ.val x y ↔
      D'.liftStep η.val (periodicSwap n p x) (periodicSwap n p y)) (x : ℤ) :
    η.liftedHRV (periodicSwap n p x) = periodicSwap n p (θ.liftedHRV x) :=
  θ.liftedHRV_conjugate η (periodicSwapEquiv n p hn) hstep
    (θ.periodicSwap_sink_order p hn hout) x

/-- The periodic swap preserves the actual circular HRV fiber monomial. -/
theorem hrvMonomial_periodicSwap (θ : Orientation D) (η : Orientation D')
    (p : ℤ) (hn : 2 ≤ (n : ℤ)) (hout : ∃ w, D.liftStep θ.val p w)
    (hstep : ∀ x y, D.liftStep θ.val x y ↔
      D'.liftStep η.val (periodicSwap n p x) (periodicSwap n p y)) :
    η.hrvMonomial = θ.hrvMonomial := by
  let π := Equiv.swap (D.residue p) (D.residue (p + 1))
  apply θ.hrvMonomial_conjugate η π
  exact θ.hrv_conjugate η (periodicSwapEquiv n p hn) π
    (fun x => D.residue_periodicSwap (by exact_mod_cast hn) p x)
    hstep (θ.periodicSwap_sink_order p hn hout)

end Orientation
end VerticalStripLLT.Circular

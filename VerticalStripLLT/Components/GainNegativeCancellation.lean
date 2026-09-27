import VerticalStripLLT.Components.GainScaling
import VerticalStripLLT.Components.GainExcess
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Alternating cancellation for strictly negative simple cycles. -/

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type*} (G : GainData V E)

private theorem list_sum_strictScale (M : ℕ) (l : List E) :
    (l.map (G.strictScale M).gain).sum =
      (M : ℤ) * (l.map G.gain).sum + l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map, List.sum_cons, List.length_cons, ih]
    dsimp [GainData.strictScale]
    ring

/-- A positive original gain excess cancels the subsets with strictly negative
simple cycles after the finite strict scaling. -/
theorem sum_powerset_simpleCyclesNegative_eq_zero_of_gain_excess
    [Fintype V] [DecidableEq E]
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm :
      (P.map G.head ++ Nsteps.map G.tail).Perm
        (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset,
      if G.SimpleCyclesNegative (A ∪ J) then (-1 : ℤ) ^ J.card else 0) =
      0 := by
  let M : ℕ := max (Fintype.card V) (Nsteps.length + 1)
  have hM : Fintype.card V ≤ M := by
    exact le_max_left _ _
  have hlenN : Nsteps.length < M := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hscaleExcess :
      (Nsteps.map (G.strictScale M).gain).sum <
        (P.map (G.strictScale M).gain).sum := by
    have hD : (1 : ℤ) ≤
        (P.map G.gain).sum - (Nsteps.map G.gain).sum := by
      linarith
    have hMnonneg : (0 : ℤ) ≤ M := Int.natCast_nonneg _
    have hMD : (M : ℤ) * 1 ≤
        (M : ℤ) *
          ((P.map G.gain).sum - (Nsteps.map G.gain).sum) :=
      mul_le_mul_of_nonneg_left hD hMnonneg
    have hNlen : (Nsteps.length : ℤ) < M := by
      exact_mod_cast hlenN
    have hPlen : (0 : ℤ) ≤ P.length := Int.natCast_nonneg _
    have hpositive : (Nsteps.length : ℤ) <
        (M : ℤ) *
            ((P.map G.gain).sum - (Nsteps.map G.gain).sum) + P.length := by
      linarith
    have hrewrite :
        (M : ℤ) * (P.map G.gain).sum + P.length -
            ((M : ℤ) * (Nsteps.map G.gain).sum + Nsteps.length) =
          (M : ℤ) *
              ((P.map G.gain).sum - (Nsteps.map G.gain).sum) +
            P.length - Nsteps.length := by
      ring
    have horder :
        (Nsteps.map (G.strictScale M).gain).sum <
            (P.map (G.strictScale M).gain).sum ↔
          0 < (P.map (G.strictScale M).gain).sum -
            (Nsteps.map (G.strictScale M).gain).sum := by
      constructor <;> intro h <;> linarith
    rw [horder]
    rw [list_sum_strictScale G M Nsteps, list_sum_strictScale G M P]
    rw [hrewrite]
    linarith
  have hclosed :=
    (G.strictScale M).sum_powerset_closedWalksNonpos_eq_zero_of_gain_excess
      A N P Nsteps hN hP hperm hscaleExcess
  have hiff (J : Finset E) :
      (G.strictScale M).ClosedWalksNonpos (A ∪ J) ↔
        G.SimpleCyclesNegative (A ∪ J) :=
    G.closedWalksNonpos_strictScale_iff (A ∪ J) M hM
  simpa only [hiff] using hclosed

end

end VerticalStripLLT.Components.GainData

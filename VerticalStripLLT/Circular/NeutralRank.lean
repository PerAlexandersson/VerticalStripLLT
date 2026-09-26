import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A finite weighted rank drop with one unit transferred between two edges. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

theorem weighted_edge_rank_drop
    {E E' : Type*} [Fintype E] [Fintype E']
    (σ : E ≃ E') (depth : E → ℕ) (targetDepth : E' → ℕ)
    (length : E → ℕ) (targetLength : E' → ℕ)
    (hdepth : ∀ f, targetDepth (σ f) = depth f)
    (eIn eOut : E) (hdepth_lt : depth eIn < depth eOut)
    (hin : targetLength (σ eIn) = length eIn + 1)
    (hout : targetLength (σ eOut) + 1 = length eOut)
    (hother : ∀ f, f ≠ eIn → f ≠ eOut →
      targetLength (σ f) = length f) :
    ∑ f' : E', targetDepth f' * targetLength f' <
      ∑ f : E, depth f * length f := by
  classical
  have hne : eIn ≠ eOut := by
    intro h
    subst eOut
    exact (Nat.lt_irrefl _ hdepth_lt)
  have hpoint (f : E) :
      targetDepth (σ f) * targetLength (σ f) +
          (if f = eOut then depth eOut else 0) =
        depth f * length f + (if f = eIn then depth eIn else 0) := by
    by_cases hfi : f = eIn
    · subst f
      rw [hdepth eIn, hin]
      simp [hne]
      ring
    · by_cases hfo : f = eOut
      · subst f
        rw [hdepth eOut]
        simp [hfi]
        calc
          depth eOut * targetLength (σ eOut) + depth eOut =
              depth eOut * (targetLength (σ eOut) + 1) := by
                ring
          _ = depth eOut * length eOut := by rw [hout]
      · rw [hdepth f, hother f hfi hfo]
        simp [hfi, hfo]
  have hsum :
      (∑ f : E, targetDepth (σ f) * targetLength (σ f)) + depth eOut =
        (∑ f : E, depth f * length f) + depth eIn := by
    have hp :
        (∑ f : E,
          (targetDepth (σ f) * targetLength (σ f) +
            (if f = eOut then depth eOut else 0))) =
          ∑ f : E,
            (depth f * length f +
              (if f = eIn then depth eIn else 0)) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact hpoint f
    simpa [Finset.sum_add_distrib, hne] using hp
  have hreindex :
      (∑ f' : E', targetDepth f' * targetLength f') =
        ∑ f : E, targetDepth (σ f) * targetLength (σ f) := by
    exact (σ.sum_comp (fun f' => targetDepth f' * targetLength f')).symm
  rw [hreindex]
  lia

end VerticalStripLLT.Circular

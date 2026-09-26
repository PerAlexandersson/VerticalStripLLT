import VerticalStripLLT.Circular.DDResolvedMeasure
import VerticalStripLLT.Circular.DDResolvedTransport
import VerticalStripLLT.Circular.NeutralTermination
import VerticalStripLLT.Circular.GeometricArea
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WellFounded

/-! Termination of auxiliary segments made of concrete DD resolutions and
neutral bounces. This relation omits R1 strictification and deletion branches;
termination does not assert existence of a next move or the final area induction. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

inductive LocalEliminationStep {n : ℕ} : Diagram n → Diagram n → Prop
  | dd {D : Diagram n} {t : ℤ} (B : D.DDLocalData t) (ht : D.EligibleDE t) :
      LocalEliminationStep D B.resolved
  | neutral {D D' : Diagram n} (B : FullNeutralBounce D D') :
      LocalEliminationStep D D'

abbrev LocalMeasure := ℕ ×ₗ ℕ

noncomputable def localMeasure {n : ℕ} (D : Diagram n) : LocalMeasure :=
  toLex (D.strict.card, D.strictRank)

theorem LocalEliminationStep.preserves_acyclic {n : ℕ} {D D' : Diagram n}
    (S : LocalEliminationStep D D') (ha : D.edgeData.Admissible ∅) :
    D'.edgeData.Admissible ∅ := by
  cases S with
  | dd B ht => exact B.resolved_admissible ht ha
  | neutral B => exact B.preserves_acyclic ha

theorem LocalEliminationStep.measure_lt {n : ℕ} {D D' : Diagram n}
    (S : LocalEliminationStep D D') (ha : D.edgeData.Admissible ∅) :
    localMeasure D' < localMeasure D := by
  cases S with
  | dd B _ =>
      rw [localMeasure, localMeasure, Prod.Lex.toLex_lt_toLex]
      left
      have hc := B.resolved_strict_card
      lia
  | neutral B =>
      rw [localMeasure, localMeasure, Prod.Lex.toLex_lt_toLex]
      right
      refine ⟨?_, ?_⟩
      · exact B.strict_card_eq ha
      · exact B.strictRank_lt ha

theorem not_admissible_of_infinite_local_elimination {n : ℕ}
    (D : ℕ → Diagram n)
    (step : ∀ i, LocalEliminationStep (D i) (D (i + 1))) :
    ¬ (D 0).edgeData.Admissible ∅ := by
  intro h0
  have ha : ∀ i, (D i).edgeData.Admissible ∅ := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih => exact (step i).preserves_acyclic ih
  let M : ℕ → LocalMeasure := fun i => localMeasure (D i)
  have hdesc : ∀ i, M (i + 1) < M i := by
    intro i
    exact (step i).measure_lt (ha i)
  have hacc : Acc ((· < ·) : LocalMeasure → LocalMeasure → Prop) (M 0) :=
    (wellFounded_lt : WellFounded ((· < ·) : LocalMeasure → LocalMeasure → Prop)).apply _
  exact (not_acc_iff_exists_descending_chain.mpr ⟨M, rfl, hdesc⟩) hacc

theorem strict_cycle_of_infinite_local_elimination {n : ℕ}
    (D : ℕ → Diagram n)
    (step : ∀ i, LocalEliminationStep (D i) (D (i + 1))) :
    ∃ v, Relation.TransGen ((D 0).edgeData.selected ∅) v v := by
  have h := not_admissible_of_infinite_local_elimination D step
  simpa only [EdgeData.Admissible, not_forall, not_not] using h

theorem coloringLLT_eq_zero_of_infinite_local_elimination {n : ℕ}
    (D : ℕ → Diagram n)
    (step : ∀ i, LocalEliminationStep (D i) (D (i + 1))) (m : ℕ) :
    (D 0).coloringLLT m = 0 :=
  coloringLLT_eq_zero_of_not_admissible_empty (D 0)
    (not_admissible_of_infinite_local_elimination D step) m

theorem shiftedOrientationExpansion_eq_zero_of_infinite_local_elimination {n : ℕ}
    (D : ℕ → Diagram n)
    (step : ∀ i, LocalEliminationStep (D i) (D (i + 1))) :
    shiftedOrientationExpansion (D 0) = 0 :=
  shiftedOrientationExpansion_eq_zero_of_not_admissible_empty (D 0)
    (not_admissible_of_infinite_local_elimination D step)

end Diagram
end VerticalStripLLT.Circular

import VerticalStripLLT.Components.DiagramProof.Foundation.WeakBlocks
import VerticalStripLLT.Components.ForwardHRVBasic

/-! A disconnected restricted core forces a selected edge out of the initial vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

/-- If deleting the initial vertex disconnects a connected state, a selected edge from `0`
ends at a vertex not weakly reachable from `a` in the core. -/
theorem exists_initial_vertex_obstruction
    {k : ℕ} {D : Diagram (k + 2)} {E : Diagram (k + 1)}
    (hD : Forward D) (θ : Orientation D) (α : Orientation E)
    (hinside : ∀ u v, E.edgeData.selected α.val u v ↔
      D.edgeData.selected θ.val u.succ v.succ)
    (hconn : SelectedConnected θ) (a : Fin (k + 1))
    (hnot : ¬ SelectedConnected α) :
    ∃ v : Fin (k + 1), D.edgeData.selected θ.val 0 v.succ ∧
      ¬ WeakReach α a v := by
  by_contra hnone
  push Not at hnone
  have hall (v : Fin (k + 1)) (hv : D.edgeData.selected θ.val 0 v.succ) :
      WeakReach α a v := hnone v hv
  let φ : Fin (k + 2) → Fin (k + 1) :=
    Fin.cases a (fun v => v)
  have hmap (u v : Fin (k + 2))
      (huv : D.edgeData.selected θ.val u v) :
      WeakReach α (φ u) (φ v) := by
    cases u using Fin.cases with
    | zero =>
        cases v using Fin.cases with
        | zero => exact Relation.EqvGen.refl _
        | succ v =>
            apply hall v
            simpa [φ] using huv
    | succ u =>
        cases v using Fin.cases with
        | zero =>
            have hlt := θ.selected_lt_of_forward hD huv
            exact ((not_lt_of_ge (Fin.zero_le _)) hlt).elim
        | succ v =>
            apply Relation.EqvGen.rel
            exact (hinside u v).mpr huv
  have hweak (u v : Fin (k + 2))
      (huv : WeakReach θ u v) : WeakReach α (φ u) (φ v) := by
    induction huv with
    | refl => exact Relation.EqvGen.refl _
    | rel _ _ h => exact hmap _ _ h
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  apply hnot
  intro u v
  have huv := hweak u.succ v.succ (hconn u.succ v.succ)
  simpa [φ] using huv

end VerticalStripLLT.Circular.DiagramProof

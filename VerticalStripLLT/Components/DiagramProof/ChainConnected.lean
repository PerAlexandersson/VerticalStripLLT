import VerticalStripLLT.Components.DiagramProof.PathTransport
import VerticalStripLLT.Components.DiagramProof.RelationPaths
import VerticalStripLLT.Components.DiagramProof.WeakBlocks
import Mathlib.Tactic.Linarith

/-! Connectivity and the extreme cover supplied by a selected consecutive chain. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram (n + 1)}

/-- Every vertex reaches the last vertex along an exact selected root row and positive chain. -/
theorem reachable_last_of_selected_chain (θ : Orientation D)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v, 0 < u → u.val + 1 = v.val →
      D.edgeData.selected θ.val u v)
    (v : Fin (n + 1)) :
    Relation.ReflTransGen (D.edgeData.selected θ.val) v (Fin.last n) := by
  have hroot : D.edgeData.selected θ.val 0 (Fin.last n) := (hrow _).mpr rfl
  have aux : ∀ k, ∀ v : Fin (n + 1), n - v.val = k →
      Relation.ReflTransGen (D.edgeData.selected θ.val) v (Fin.last n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hgap
      by_cases hvzero : v = 0
      · subst v
        exact Relation.ReflTransGen.single hroot
      by_cases hvlast : v = Fin.last n
      · subst v
        exact Relation.ReflTransGen.refl
      have hvlt : v.val < n := by
        have hvbound := v.isLt
        have hvne : v.val ≠ n := fun h => hvlast (Fin.ext h)
        lia
      let w : Fin (n + 1) := ⟨v.val + 1, by lia⟩
      have hvpos : 0 < v := Fin.pos_iff_ne_zero.mpr hvzero
      have hstep : D.edgeData.selected θ.val v w := hchain v w hvpos rfl
      apply (Relation.ReflTransGen.single hstep).trans
      apply ih (n - w.val) ?_ w rfl
      rw [← hgap]
      change n - (v.val + 1) < n - v.val
      lia
  exact aux (n - v.val) v rfl

/-- A selected consecutive chain connects the full selected graph. -/
theorem selectedConnected_of_selected_chain (θ : Orientation D)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v, 0 < u → u.val + 1 = v.val →
      D.edgeData.selected θ.val u v) :
    SelectedConnected θ := by
  intro u v
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
      (reachable_last_of_selected_chain θ hrow hchain u))
    (Relation.EqvGen.symm _ _
      (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
        (reachable_last_of_selected_chain θ hrow hchain v)))

/-- When the last vertex is positive, the exact root row makes its edge a cover. -/
theorem cover_zero_last_of_selected_chain (hforward : Forward D) (θ : Orientation D)
    (hn : 0 < n) (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = Fin.last n) :
    Cover θ 0 (Fin.last n) := by
  have hroot : D.edgeData.selected θ.val 0 (Fin.last n) := (hrow _).mpr rfl
  refine ⟨by change 0 < n; exact hn, Relation.ReflTransGen.single hroot, ?_⟩
  intro w hzero_w hwlast hw
  rcases hw.1.cases_head with hzero | ⟨q, hzero_q, hqw⟩
  · exact hzero_w.ne hzero
  · have hqlast : q = Fin.last n := (hrow q).mp hzero_q
    subst q
    exact (not_le_of_gt hwlast) (reachable_le
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) hqw)

/-- A positive selected consecutive chain supplies both connectivity and its extreme cover. -/
theorem selectedConnected_and_cover_of_selected_chain (hforward : Forward D)
    (θ : Orientation D) (hn : 0 < n)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v, 0 < u → u.val + 1 = v.val →
      D.edgeData.selected θ.val u v) :
    SelectedConnected θ ∧ Cover θ 0 (Fin.last n) :=
  ⟨selectedConnected_of_selected_chain θ hrow hchain,
    cover_zero_last_of_selected_chain hforward θ hn hrow⟩

end VerticalStripLLT.Circular.DiagramProof

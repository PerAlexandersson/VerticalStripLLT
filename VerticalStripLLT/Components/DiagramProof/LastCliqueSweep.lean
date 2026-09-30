import VerticalStripLLT.Components.DiagramProof.OrderedSweep

/-! Sweeping selected edges from the last omitted gap into its left endpoint. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Sweep every selected edge from the gap `(c,e)` into `e` across `a → e`.
The resulting state has no selected gap-to-final edge and agrees exactly with the
source on the prefix together with the final vertex. -/
theorem exists_lastCliqueSweep (hforward : Forward D) (θ : Orientation D)
    (a c e : Fin n) (hac : a < c) (hce : c < e) (hae : Cover θ a e) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ Cover η a e ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        incomingSweepRelation (D.edgeData.selected θ.val) a c e u v) ∧
      (∀ x, c < x → x < e → ¬ D.edgeData.selected η.val x e) ∧
      (∀ u v, (u ≤ c ∨ u = e) → (v ≤ c ∨ v = e) →
        (D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v)) := by
  obtain ⟨η, hpath, haeη, hrelation⟩ :=
    exists_incomingSweep hforward θ a c e hac hce hae
  refine ⟨η, hpath, haeη, hrelation, ?_, ?_⟩
  · intro x hcx hxe hxelected
    rw [hrelation] at hxelected
    rcases hxelected with hnew | hold
    · exact (lt_irrefl _ hnew.1).elim
    · exact hold.2 ⟨rfl, hcx⟩
  · intro u v hu hv
    rw [hrelation]
    constructor
    · intro hselected
      rcases hselected with hnew | hold
      · rcases hv with hvc | rfl
        · exact (not_lt_of_ge hvc hnew.2.1).elim
        · exact (lt_irrefl _ hnew.1).elim
      · exact hold.1
    · intro hselected
      apply Or.inr
      refine ⟨hselected, ?_⟩
      rintro ⟨rfl, hcu⟩
      rcases hu with huc | rfl
      · exact (not_lt_of_ge huc hcu).elim
      · exact (lt_irrefl _ (θ.selected_lt_of_forward hforward hselected)).elim

end VerticalStripLLT.Circular.DiagramProof

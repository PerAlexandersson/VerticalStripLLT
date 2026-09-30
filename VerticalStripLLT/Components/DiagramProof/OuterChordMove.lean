import VerticalStripLLT.Components.DiagramProof.ColumnSweep
import VerticalStripLLT.Components.DiagramProof.ChainRepair

/-! The outer-chord move `A - 13 + 1n`, with all other edges restored. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- If `13` and `2n` are selected and `1n` is absent, the column sweep and
four-flip repair replace exactly `13` by `1n`. -/
theorem exists_complete_outerChordMove {n : ℕ}
    (θ : Orientation (completeDiagram n)) (i j t : Fin (n + 1))
    (hi : i.val = 1) (hj : j.val = 2) (ht : t.val = 3) (htn : t < Fin.last n)
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (h13 : (completeDiagram n).edgeData.selected θ.val i t)
    (h2n : (completeDiagram n).edgeData.selected θ.val j (Fin.last n))
    (h1n : ¬ (completeDiagram n).edgeData.selected θ.val i (Fin.last n)) :
    ∃ η : Orientation (completeDiagram n),
      Relation.ReflTransGen (Flip (completeDiagram n)) θ η ∧
      (∀ u v, (completeDiagram n).edgeData.selected η.val u v ↔
        (u = i ∧ v = Fin.last n) ∨
          ((completeDiagram n).edgeData.selected θ.val u v ∧ ¬ (u = i ∧ v = t))) := by
  have h0i : (0 : Fin (n + 1)) < i := by change 0 < i.val; lia
  have hij : i < j := by change i.val < j.val; lia
  have hjt : j < t := by change j.val < t.val; lia
  have hit := hij.trans hjt
  have h0t := h0i.trans hit
  have hin := hit.trans htn
  have hjn := hjt.trans htn
  have h12 := hchain i j h0i (by lia)
  have h23 := hchain j t (h0i.trans hij) (by lia)
  obtain ⟨γ, hθγ, _, hγ⟩ := exists_columnSweep (complete_forward n) θ i j hi hj hjn
    hrow h12 h2n h1n
  let R := fun u v => (u = i ∧ v = Fin.last n) ∨
    ((completeDiagram n).edgeData.selected θ.val u v ∧ ¬ (u = i ∧ v = t))
  have hnatural : ∀ u v, R u v → ∃ e : Edge (completeDiagram n).area,
      e.tail = u ∧ e.head = v := by
    intro u v h
    apply (complete_naturalEdge_iff n u v).mpr
    rcases h with ⟨rfl, rfl⟩ | ⟨h, _⟩
    · exact hin
    · exact θ.selected_lt_of_forward (complete_forward n) h
  let η := ofSelectedRelation (complete_forward n) R hnatural (by simp)
  have hη (u v) : (completeDiagram n).edgeData.selected η.val u v ↔ R u v :=
    selected_ofSelectedRelation ..
  have hγrow : ∀ v, (completeDiagram n).edgeData.selected γ.val 0 v ↔ v = Fin.last n := by
    intro v
    rw [hγ]
    simp [h0i.ne, hrow]
  have hγchain : ∀ u v : Fin (n + 1), t ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected γ.val u v := by
    intro u v htu huv
    rw [hγ]
    exact Or.inr ⟨hchain u v (h0t.trans_le htu) huv,
      fun h => (not_le_of_gt hit) (h.1 ▸ htu)⟩
  have hγ13 : (completeDiagram n).edgeData.selected γ.val i t := by
    rw [hγ]
    exact Or.inr ⟨h13, by simp [hjt.ne.symm]⟩
  have hγ23 : (completeDiagram n).edgeData.selected γ.val j t := by
    rw [hγ]
    exact Or.inr ⟨h23, by simp [hij.ne.symm]⟩
  have hγ12 : ¬ (completeDiagram n).edgeData.selected γ.val i j := by
    rw [hγ]
    simp [hjn.ne]
  have hrepair (u v) : (completeDiagram n).edgeData.selected η.val u v ↔
      (u = i ∧ v = j) ∨
        ((completeDiagram n).edgeData.selected γ.val u v ∧ ¬ (u = i ∧ v = t)) := by
    rw [hη, hγ]
    dsimp [R]
    have hjne := hjt.ne
    have htne := htn.ne
    have hjnne := hjn.ne
    grind only
  have hγη := complete_chain_repair γ η i j t hi hj ht hγrow hγchain hγ13 hγ23 hγ12 hrepair
  exact ⟨η, hθγ.trans hγη, hη⟩

end

end VerticalStripLLT.Circular.DiagramProof

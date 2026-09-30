import VerticalStripLLT.Components.DiagramProof.OrderedSweep
import VerticalStripLLT.Components.DiagramProof.RelationExchange
import VerticalStripLLT.Components.DiagramProof.ChainConnected

/-! The incoming sweep, bottom flip, and outgoing restoration of CC5--CC6. -/

namespace VerticalStripLLT.Circular.DiagramProof

private theorem columnSweep_relation {V : Type*} [LinearOrder V]
    (R : V → V → Prop) (a b c d : V) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (hrow : ∀ v, R a v ↔ v = d)
    (u v : V) :
    outgoingSweepRelation
      (exchangeRelation (incomingSweepRelation R a b d) b c a b) a d d u v ↔
      exchangeRelation R b c b d u v := by
  simp only [outgoingSweepRelation, exchangeRelation, incomingSweepRelation_iff]
  have had := hab.trans (hbc.trans hcd)
  have hbd := hbc.trans hcd
  have hac := hab.trans hbc
  have hroot := (hrow d).mpr rfl
  have hRau := hrow u
  have hRav := hrow v
  have huv : R u v → u < v := fun h => hforward h
  have hud : R u d → u < d := fun h => hforward h
  have hvd : R v d → v < d := fun h => hforward h
  grind only

/-- Sweep the last column, replace `12` by `01`, and restore the column.
The exact endpoint replaces `12` by `1n`; every other selected edge is restored. -/
theorem exists_columnSweep {n : ℕ} {D : Diagram (n + 1)}
    (hforward : Forward D) (θ : Orientation D)
    (i j : Fin (n + 1)) (hi : i.val = 1) (hj : j.val = 2)
    (hjn : j < Fin.last n)
    (hrow : ∀ v, D.edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hij : D.edgeData.selected θ.val i j)
    (hjnSelected : D.edgeData.selected θ.val j (Fin.last n))
    (hin : ¬ D.edgeData.selected θ.val i (Fin.last n)) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Cover η 0 (Fin.last n) ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = i ∧ v = Fin.last n) ∨
          (D.edgeData.selected θ.val u v ∧ ¬ (u = i ∧ v = j))) := by
  have h0i : (0 : Fin (n + 1)) < i := by change 0 < i.val; lia
  have hijlt : i < j := by change i.val < j.val; lia
  have hinlt := hijlt.trans hjn
  have h0j := h0i.trans hijlt
  have h0n := h0j.trans hjn
  have hn : 0 < n := h0n
  have hcover := cover_zero_last_of_selected_chain hforward θ hn hrow
  obtain ⟨β, hθβ, hβcover, hβ⟩ :=
    exists_incomingSweep hforward θ 0 i (Fin.last n) h0i hinlt hcover
  have hβij : D.edgeData.selected β.val i j := by
    rw [hβ, incomingSweepRelation_iff]
    exact Or.inr ⟨hij, by simp [hjn.ne]⟩
  have hβ0j : D.edgeData.selected β.val 0 j := by
    rw [hβ, incomingSweepRelation_iff]
    exact Or.inl ⟨hjn, hijlt, rfl, hjnSelected⟩
  have hβijCover : Cover β i j := by
    apply relationCover_of_first_outgoing
      (fun {_ _} h => β.selected_lt_of_forward hforward h) hβij
    intro z hiz hzj _
    change i.val < z.val at hiz
    change z.val < j.val at hzj
    lia
  have hβ0jCover : Cover β 0 j := by
    apply relationCover_of_first_outgoing
      (fun {_ _} h => β.selected_lt_of_forward hforward h) hβ0j
    intro z h0z hzj hz
    have hzi : z = i := by
      apply Fin.ext
      change 0 < z.val at h0z
      change z.val < j.val at hzj
      lia
    subst z
    rw [hβ, incomingSweepRelation_iff] at hz
    rcases hz with ⟨_, hii, _⟩ | ⟨hs, _⟩
    · exact (lt_irrefl i) hii
    · exact hinlt.ne ((hrow i).mp hs)
  have hβincoming (z : Fin (n + 1)) (hz : 0 < z) :
      ¬ D.edgeData.selected β.val z (Fin.last n) := by
    intro hs
    rw [hβ, incomingSweepRelation_iff] at hs
    rcases hs with ⟨hlt, _⟩ | ⟨hs, hnot⟩
    · exact (lt_irrefl (Fin.last n)) hlt
    · have hle : z ≤ i := le_of_not_gt (fun h => hnot ⟨rfl, h⟩)
      have hzi : z = i := by
        apply Fin.ext
        change 0 < z.val at hz
        change z.val ≤ i.val at hle
        lia
      exact hin (hzi ▸ hs)
  obtain ⟨γ, hβγ, _, _, hγ⟩ :=
    exists_incomingSwap_of_covers hforward β 0 i j hβijCover hβ0jCover h0i
  have hγroot : D.edgeData.selected γ.val 0 (Fin.last n) := by
    rw [hγ]
    exact Or.inr ⟨selected_of_cover hforward hβcover, by simp [h0i.ne]⟩
  have hγcover : Cover γ 0 (Fin.last n) := by
    apply relationCover_of_last_incoming
      (fun {_ _} h => γ.selected_lt_of_forward hforward h) hγroot
    intro z hz _ hs
    rw [hγ] at hs
    rcases hs with ⟨_, hni⟩ | ⟨hs, _⟩
    · exact hinlt.ne hni.symm
    · exact hβincoming z hz hs
  obtain ⟨η, hγη, hηcover, hη⟩ :=
    exists_outgoingSweep_of_le hforward γ 0 (Fin.last n) (Fin.last n) h0n le_rfl hγcover
  refine ⟨η, hθβ.trans ((Relation.ReflTransGen.single hβγ).trans hγη), hηcover, ?_⟩
  intro u v
  rw [hη]
  have hγrel : D.edgeData.selected γ.val =
      exchangeRelation (incomingSweepRelation (D.edgeData.selected θ.val) 0 i (Fin.last n))
        i j 0 i := by
    funext x y
    apply propext
    rw [hγ, hβ]
    rfl
  rw [hγrel]
  exact columnSweep_relation _ 0 i j (Fin.last n) h0i hijlt hjn
    (fun {_ _} h => θ.selected_lt_of_forward hforward h) hrow u v

end VerticalStripLLT.Circular.DiagramProof

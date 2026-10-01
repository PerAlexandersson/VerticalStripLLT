import VerticalStripLLT.Components.DiagramProof.Preparation.TerminalChildren
import VerticalStripLLT.Components.DiagramProof.Preparation.SingleCorner

/-! Prepare a connected state with one extreme corner for induction on the last vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

include hforward

/-- A connected common-cover state at a single extreme corner reaches a state
whose prefix is connected and whose two edges from the least vertex cover. -/
theorem exists_connected_prefix_of_single_corner (θ : Orientation D)
    (hC : F.CommonCover θ) (hconnected : SelectedConnected θ)
    {e : Edge D.area} {z j t : Fin n} (hedges : F.edges = {e})
    (hetail : e.tail = z) (hehead : e.head = t)
    (hz : ∀ v, z ≤ v) (ht : ∀ v, v ≤ t) (hzj : z < j) (hjt : j < t)
    (hj : ∀ v, v < t → v ≤ j) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Cover η z j ∧ Cover η z t ∧
      (∀ v, D.edgeData.selected η.val z v ↔ v = j ∨ v = t) ∧
      (¬ D.edgeData.selected η.val j t) ∧
      ∀ v, v ≤ j → Relation.ReflTransGen (D.edgeData.selected η.val) v j := by
  obtain ⟨α, hθα, _, hrowα⟩ :=
    F.exists_preparation_of_singleton hforward hedges hetail hehead ht θ hC
  have hrowUnique : ∀ u v, D.edgeData.selected α.val z u →
      D.edgeData.selected α.val z v → u = v := by
    intro u v hu hv
    exact ((hrowα u).mp hu).trans ((hrowα v).mp hv).symm
  obtain ⟨β, hαβ, huniqueβ, hβrow⟩ :=
    exists_rightUnique_covers_preserving_minimal_row hforward α z hz hrowUnique
  have hrowβ : ∀ v, D.edgeData.selected β.val z v ↔ v = t :=
    fun v => (hβrow v).trans (hrowα v)
  have hconnectedβ : SelectedConnected β :=
    (selectedConnected_iff_of_reachable (hθα.trans hαβ)).mp hconnected
  have hchildβ : Cover β j t := by
    refine ⟨hjt, reachable_top_of_connected_of_rightUnique_covers
      hforward huniqueβ hconnectedβ t ht j, ?_⟩
    intro v hjv hvt _
    exact not_lt_of_ge (hj v hvt) hjv
  obtain ⟨γ, hβγ, huniqueγ, hchildγ, hrowγ, hchildrenγ⟩ :=
    exists_merge_other_children hforward β z j t hz hjt ht hj huniqueβ hchildβ hrowβ
  have hconnectedγ : SelectedConnected γ :=
    (selectedConnected_iff_of_reachable hβγ).mp hconnectedβ
  obtain ⟨η, hγη, hzjη, hztη, hη, hprefix⟩ :=
    exists_move_last_child hforward γ z j t hz hzj hjt ht huniqueγ hconnectedγ
      hchildγ hrowγ hchildrenγ
  refine ⟨η, ((hθα.trans hαβ).trans hβγ).tail hγη, hzjη, hztη, ?_, ?_, hprefix⟩
  · intro v
    rw [hη]
    simp [hzj.ne, hrowγ v]
  · rw [hη]
    simp [hzj.ne.symm]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily

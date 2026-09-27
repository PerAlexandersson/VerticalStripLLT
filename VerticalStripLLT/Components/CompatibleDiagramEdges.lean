import VerticalStripLLT.Components.CompatibleLiftOrder
import VerticalStripLLT.Components.IntervalDiagram
import VerticalStripLLT.Circular.FirstBounceOrientationData

/-! An actual ordinary diagram on the ranks of compatible chosen lifts. -/

namespace VerticalStripLLT.Circular.Diagram

open Classical

noncomputable section

variable {n : ℕ} (D : Diagram n) (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
variable (hmono : StrictMono (q ∘ σ))

/-- The compatible natural intervals form an undecorated diagram in rank order. -/
def compatibleDiagram : Diagram n :=
  ofIntervalRelation (D.compatibleLiftRelation q σ)
    (fun h hij hjk => D.compatibleLiftRelation_interval hmono h hij hjk) D.area.positive

@[simp]
theorem compatibleDiagram_strict : (D.compatibleDiagram q σ hmono).strict = ∅ := rfl

theorem compatibleDiagram_forward (e : Edge (D.compatibleDiagram q σ hmono).area) :
    e.tail < e.head :=
  ofIntervalRelation_forward _ (fun h => D.compatibleLiftRelation_forward hmono h)
    _ _ e

theorem compatibleDiagram_naturalEdge_iff (i j : Fin n) :
    (∃ e : Edge (D.compatibleDiagram q σ hmono).area, e.tail = i ∧ e.head = j) ↔
      D.compatibleLiftRelation q σ i j :=
  ofIntervalRelation_naturalEdge_iff _
    (fun h => D.compatibleLiftRelation_forward hmono h) _ _ i j

/-- A ranked natural edge is realized by its unique original natural interval. -/
def compatibleEdge (e : Edge (D.compatibleDiagram q σ hmono).area) : Edge D.area :=
  (ofIntervalRelation_edge_rel _
    (fun h => D.compatibleLiftRelation_forward hmono h) _ _ e).choose

theorem compatibleEdge_lift (e : Edge (D.compatibleDiagram q σ hmono).area) :
    D.naturalLift (D.compatibleEdge q σ hmono e) (q (σ e.tail)) (q (σ e.head)) :=
  (ofIntervalRelation_edge_rel _
    (fun h => D.compatibleLiftRelation_forward hmono h) _ _ e).choose_spec

variable (hq : ∀ v, D.residue (q v) = v)

include hq

theorem compatibleEdge_tail (e : Edge (D.compatibleDiagram q σ hmono).area) :
    (D.compatibleEdge q σ hmono e).tail = σ e.tail :=
  ((D.naturalLift_chosen_iff hq _ _ _).mp (D.compatibleEdge_lift q σ hmono e)).1

theorem compatibleEdge_head (e : Edge (D.compatibleDiagram q σ hmono).area) :
    (D.compatibleEdge q σ hmono e).head = σ e.head :=
  ((D.naturalLift_chosen_iff hq _ _ _).mp (D.compatibleEdge_lift q σ hmono e)).2.1

theorem compatibleEdge_injective : Function.Injective (D.compatibleEdge q σ hmono) := by
  intro e f hef
  apply (D.compatibleDiagram q σ hmono).edge_eq_of_endpoints
  · apply σ.injective
    rw [← D.compatibleEdge_tail q σ hmono hq e,
      ← D.compatibleEdge_tail q σ hmono hq f, hef]
  · apply σ.injective
    rw [← D.compatibleEdge_head q σ hmono hq e,
      ← D.compatibleEdge_head q σ hmono hq f, hef]

/-- Exactly the natural edges balanced by these lifts occur in the ranked diagram. -/
theorem mem_range_compatibleEdge_iff (e : Edge D.area) :
    e ∈ Set.range (D.compatibleEdge q σ hmono) ↔
      q e.head - q e.tail = (e.length.val : ℤ) := by
  constructor
  · rintro ⟨f, rfl⟩
    have h := (D.naturalLift_chosen_iff hq _ _ _).mp
      (D.compatibleEdge_lift q σ hmono f)
    rw [h.1, h.2.1]
    exact h.2.2
  · intro he
    have hrel : D.compatibleLiftRelation q σ (σ.symm e.tail) (σ.symm e.head) := by
      refine ⟨e, ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact (D.naturalLift_chosen_iff hq e e.tail e.head).mpr ⟨rfl, rfl, he⟩
    obtain ⟨f, hft, hfh⟩ :=
      (D.compatibleDiagram_naturalEdge_iff q σ hmono _ _).mpr hrel
    refine ⟨f, D.edge_eq_of_endpoints ?_ ?_⟩
    · rw [D.compatibleEdge_tail q σ hmono hq f, hft, Equiv.apply_symm_apply]
    · rw [D.compatibleEdge_head q σ hmono hq f, hfh, Equiv.apply_symm_apply]

end

end VerticalStripLLT.Circular.Diagram

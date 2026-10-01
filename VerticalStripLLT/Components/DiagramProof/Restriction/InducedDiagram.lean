import VerticalStripLLT.Components.DiagramProof.Corners.CliqueEdges
import VerticalStripLLT.Components.IntervalDiagram

/-! The natural diagram induced on an increasing list of vertices. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n} (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)

/-- Natural edges on the chosen vertices, before compressing their labels. -/
def inducedNaturalRelation (u v : Fin (k + 1)) : Prop :=
  ∃ e : Edge D.area, e.tail = ι u ∧ e.head = ι v

include hD in
theorem inducedNaturalRelation_forward {u v : Fin (k + 1)}
    (h : inducedNaturalRelation (D := D) ι u v) : u < v := by
  obtain ⟨e, ht, hh⟩ := h
  apply ι.lt_iff_lt.mp
  simpa only [← ht, ← hh] using hD e

include hD in
theorem inducedNaturalRelation_interval {u v w : Fin (k + 1)}
    (h : inducedNaturalRelation (D := D) ι u w) (huv : u < v) (hvw : v < w) :
    inducedNaturalRelation (D := D) ι u v ∧ inducedNaturalRelation (D := D) ι v w := by
  obtain ⟨e, ht, hh⟩ := h
  have he := D.naturalLift_of_tail_lt_head e (hD e)
  constructor
  · exact exists_edge_of_naturalLift_of_le he ht.le (ι.strictMono huv)
      ((ι.strictMono hvw).le.trans hh.symm.le)
  · exact exists_edge_of_naturalLift_of_le he
      (ht.le.trans (ι.strictMono huv).le) (ι.strictMono hvw) hh.symm.le

/-- The induced natural graph as an actual diagram. Strict markings are not yet added. -/
def inducedUndecorated : Diagram (k + 1) :=
  Diagram.ofIntervalRelation (inducedNaturalRelation (D := D) ι)
    (fun h huv hvw => inducedNaturalRelation_interval hD ι h huv hvw) (Nat.zero_lt_succ k)

@[simp]
theorem inducedUndecorated_strict : (inducedUndecorated hD ι).strict = ∅ := rfl

theorem inducedUndecorated_forward : Forward (inducedUndecorated hD ι) :=
  Diagram.ofIntervalRelation_forward _ (fun h => inducedNaturalRelation_forward hD ι h)
    _ _

theorem inducedUndecorated_naturalEdge_iff (u v : Fin (k + 1)) :
    (∃ e : Edge (inducedUndecorated hD ι).area, e.tail = u ∧ e.head = v) ↔
      ∃ f : Edge D.area, f.tail = ι u ∧ f.head = ι v :=
  Diagram.ofIntervalRelation_naturalEdge_iff _
    (fun h => inducedNaturalRelation_forward hD ι h) _ _ u v

/-- An induced edge has a unique ambient edge with the embedded endpoints. -/
def inducedEdge (e : Edge (inducedUndecorated hD ι).area) : Edge D.area :=
  ((inducedUndecorated_naturalEdge_iff hD ι e.tail e.head).mp ⟨e, rfl, rfl⟩).choose

/-- The tail of an induced edge is the image of its tail. -/
@[simp]
theorem inducedEdge_tail (e : Edge (inducedUndecorated hD ι).area) :
    (inducedEdge hD ι e).tail = ι e.tail :=
  ((inducedUndecorated_naturalEdge_iff hD ι e.tail e.head).mp ⟨e, rfl, rfl⟩).choose_spec.1

@[simp]
theorem inducedEdge_head (e : Edge (inducedUndecorated hD ι).area) :
    (inducedEdge hD ι e).head = ι e.head :=
  ((inducedUndecorated_naturalEdge_iff hD ι e.tail e.head).mp ⟨e, rfl, rfl⟩).choose_spec.2

theorem inducedEdge_injective : Function.Injective (inducedEdge hD ι) := by
  intro e f hef
  apply (inducedUndecorated hD ι).endpointEmbedding.injective
  apply Prod.ext
  · apply ι.injective
    change ι e.tail = ι f.tail
    rw [← inducedEdge_tail, ← inducedEdge_tail, hef]
  · apply ι.injective
    change ι e.head = ι f.head
    rw [← inducedEdge_head, ← inducedEdge_head, hef]

theorem mem_range_inducedEdge_iff (e : Edge D.area) :
    e ∈ Set.range (inducedEdge hD ι) ↔ ∃ u v, ι u = e.tail ∧ ι v = e.head := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.tail, f.head, (inducedEdge_tail hD ι f).symm,
      (inducedEdge_head hD ι f).symm⟩
  · rintro ⟨u, v, hu, hv⟩
    obtain ⟨f, ht, hh⟩ := (inducedUndecorated_naturalEdge_iff hD ι u v).mpr
      ⟨e, hu.symm, hv.symm⟩
    refine ⟨f, D.endpointEmbedding.injective (Prod.ext ?_ ?_)⟩
    · exact (inducedEdge_tail hD ι f).trans ((congrArg ι ht).trans hu)
    · exact (inducedEdge_head hD ι f).trans ((congrArg ι hh).trans hv)

end

end VerticalStripLLT.Circular.DiagramProof

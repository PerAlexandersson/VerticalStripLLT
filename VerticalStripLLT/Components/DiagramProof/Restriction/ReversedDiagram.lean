import VerticalStripLLT.Components.DiagramProof.Corners.CornerMaximality
import VerticalStripLLT.Components.IntervalDiagram
import VerticalStripLLT.Components.DiagramProof.Corners.CliqueEdges

/-! The interval diagram obtained by reversing the column order. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Natural edges after reversing the order of the columns. -/
def reversedNaturalRelation (D : Diagram n) (u v : Fin n) : Prop :=
  ∃ e : Edge D.area, e.tail = v.rev ∧ e.head = u.rev

private theorem reversedNaturalRelation_forward (hD : Forward D)
    {u v : Fin n} (h : reversedNaturalRelation D u v) : u < v := by
  obtain ⟨e, ht, hh⟩ := h
  exact Fin.rev_lt_rev.mp (by simpa only [ht, hh] using hD e)

private theorem reversedNaturalRelation_interval (hD : Forward D)
    {u v w : Fin n} (h : reversedNaturalRelation D u w) (huv : u < v)
    (hvw : v < w) :
    reversedNaturalRelation D u v ∧ reversedNaturalRelation D v w := by
  obtain ⟨e, ht, hh⟩ := h
  have he := D.naturalLift_of_tail_lt_head e (hD e)
  have hwv : w.rev < v.rev := Fin.rev_lt_rev.mpr hvw
  have hvu : v.rev < u.rev := Fin.rev_lt_rev.mpr huv
  constructor
  · obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le he
      (ht.le.trans hwv.le) hvu hh.symm.le
    exact ⟨f, hft, hfh⟩
  · obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le he ht.le hwv
      (by simpa only [hh] using hvu.le)
    exact ⟨f, hft, hfh⟩

/-- The undecorated diagram whose natural edges are reversed natural edges of `D`. -/
def reversedUndecorated (hD : Forward D) : Diagram n :=
  Diagram.ofIntervalRelation (reversedNaturalRelation D)
    (fun h huv hvw => reversedNaturalRelation_interval hD h huv hvw) D.area.positive

theorem reversedUndecorated_forward (hD : Forward D) :
    Forward (reversedUndecorated hD) := by
  intro e
  exact Diagram.ofIntervalRelation_forward _
    (fun h => reversedNaturalRelation_forward hD h) _ _ e

theorem reversedUndecorated_naturalEdge_iff (hD : Forward D) (u v : Fin n) :
    (∃ e : Edge (reversedUndecorated hD).area, e.tail = u ∧ e.head = v) ↔
      ∃ f : Edge D.area, f.tail = v.rev ∧ f.head = u.rev := by
  exact Diagram.ofIntervalRelation_naturalEdge_iff _
    (fun h => reversedNaturalRelation_forward hD h) _ _ u v

/-- Reverse the endpoints of an old natural edge. -/
def reverseUndecoratedEdge (hD : Forward D) (e : Edge D.area) :
    Edge (reversedUndecorated hD).area :=
  (reversedUndecorated_naturalEdge_iff hD e.head.rev e.tail.rev).mpr
    ⟨e, by simp, by simp⟩ |>.choose

theorem reverseUndecoratedEdge_tail (hD : Forward D) (e : Edge D.area) :
    (reverseUndecoratedEdge hD e).tail = e.head.rev :=
  (reversedUndecorated_naturalEdge_iff hD e.head.rev e.tail.rev).mpr
    ⟨e, by simp, by simp⟩ |>.choose_spec.1

theorem reverseUndecoratedEdge_head (hD : Forward D) (e : Edge D.area) :
    (reverseUndecoratedEdge hD e).head = e.tail.rev :=
  (reversedUndecorated_naturalEdge_iff hD e.head.rev e.tail.rev).mpr
    ⟨e, by simp, by simp⟩ |>.choose_spec.2

/-- Recover the old edge represented by a reversed natural edge. -/
def unreversedUndecoratedEdge (hD : Forward D)
    (e : Edge (reversedUndecorated hD).area) : Edge D.area :=
  (reversedUndecorated_naturalEdge_iff hD e.tail e.head).mp ⟨e, rfl, rfl⟩ |>.choose

theorem unreversedUndecoratedEdge_tail (hD : Forward D)
    (e : Edge (reversedUndecorated hD).area) :
    (unreversedUndecoratedEdge hD e).tail = e.head.rev :=
  (reversedUndecorated_naturalEdge_iff hD e.tail e.head).mp ⟨e, rfl, rfl⟩ |>.choose_spec.1

theorem unreversedUndecoratedEdge_head (hD : Forward D)
    (e : Edge (reversedUndecorated hD).area) :
    (unreversedUndecoratedEdge hD e).head = e.tail.rev :=
  (reversedUndecorated_naturalEdge_iff hD e.tail e.head).mp ⟨e, rfl, rfl⟩ |>.choose_spec.2

private theorem unreversed_reverseUndecoratedEdge (hD : Forward D) (e : Edge D.area) :
    unreversedUndecoratedEdge hD (reverseUndecoratedEdge hD e) = e := by
  apply D.endpointEmbedding.injective
  apply Prod.ext
  · change (unreversedUndecoratedEdge hD (reverseUndecoratedEdge hD e)).tail = e.tail
    rw [unreversedUndecoratedEdge_tail, reverseUndecoratedEdge_head]
    simp
  · change (unreversedUndecoratedEdge hD (reverseUndecoratedEdge hD e)).head = e.head
    rw [unreversedUndecoratedEdge_head, reverseUndecoratedEdge_tail]
    simp

private theorem reverse_unreversedUndecoratedEdge (hD : Forward D)
    (e : Edge (reversedUndecorated hD).area) :
    reverseUndecoratedEdge hD (unreversedUndecoratedEdge hD e) = e := by
  apply (reversedUndecorated hD).endpointEmbedding.injective
  apply Prod.ext
  · change (reverseUndecoratedEdge hD (unreversedUndecoratedEdge hD e)).tail = e.tail
    rw [reverseUndecoratedEdge_tail, unreversedUndecoratedEdge_head]
    simp
  · change (reverseUndecoratedEdge hD (unreversedUndecoratedEdge hD e)).head = e.head
    rw [reverseUndecoratedEdge_head, unreversedUndecoratedEdge_tail]
    simp

private theorem reverseUndecoratedEdge_isCorner_iff (hD : Forward D) (e : Edge D.area) :
    IsCorner e ↔ IsCorner (reverseUndecoratedEdge hD e) := by
  constructor
  · intro he
    have hext := (isCorner_iff_extremal hD e).mp he
    apply (isCorner_iff_extremal (reversedUndecorated_forward hD) _).mpr
    constructor
    · intro f hf
      let f' := unreversedUndecoratedEdge hD f
      have htail : f'.tail = e.tail := by
        dsimp only [f']
        rw [unreversedUndecoratedEdge_tail]
        have hf' : f.head = e.tail.rev := by
          simpa only [reverseUndecoratedEdge_head] using hf
        simpa only [Fin.rev_rev] using congrArg Fin.rev hf'
      have hle : (unreversedUndecoratedEdge hD f).head ≤ e.head := hext.2 f' htail
      rw [unreversedUndecoratedEdge_head] at hle
      rw [reverseUndecoratedEdge_tail]
      simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr hle
    · intro f hf
      let f' := unreversedUndecoratedEdge hD f
      have hhead : f'.head = e.head := by
        dsimp only [f']
        rw [unreversedUndecoratedEdge_head]
        have hf' : f.tail = e.head.rev := by
          simpa only [reverseUndecoratedEdge_tail] using hf
        simpa only [Fin.rev_rev] using congrArg Fin.rev hf'
      have hle : e.tail ≤ (unreversedUndecoratedEdge hD f).tail := hext.1 f' hhead
      rw [unreversedUndecoratedEdge_tail] at hle
      rw [reverseUndecoratedEdge_head]
      simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr hle
  · intro he
    apply (isCorner_iff_extremal hD e).mpr
    have hext := (isCorner_iff_extremal (reversedUndecorated_forward hD)
      (reverseUndecoratedEdge hD e)).mp he
    constructor
    · intro f hf
      have htail : (reverseUndecoratedEdge hD f).tail =
          (reverseUndecoratedEdge hD e).tail := by
        rw [reverseUndecoratedEdge_tail, reverseUndecoratedEdge_tail]
        simpa only [Fin.rev_rev] using congrArg Fin.rev hf
      have hle := hext.2 (reverseUndecoratedEdge hD f) htail
      rw [reverseUndecoratedEdge_head, reverseUndecoratedEdge_head] at hle
      exact Fin.rev_le_rev.mp hle
    · intro f hf
      have hhead : (reverseUndecoratedEdge hD f).head =
          (reverseUndecoratedEdge hD e).head := by
        rw [reverseUndecoratedEdge_head, reverseUndecoratedEdge_head]
        simpa only [Fin.rev_rev] using congrArg Fin.rev hf
      have hle := hext.1 (reverseUndecoratedEdge hD f) hhead
      rw [reverseUndecoratedEdge_tail, reverseUndecoratedEdge_tail] at hle
      exact Fin.rev_le_rev.mp hle

/-- The reversed diagram inherits the old strict edges through endpoint reversal. -/
def reversedDiagram (hD : Forward D) : Diagram n where
  area := (reversedUndecorated hD).area
  strict := Finset.univ.filter (fun e =>
    unreversedUndecoratedEdge hD e ∈ D.strict)
  strict_corner := by
    intro e he
    rw [← reverse_unreversedUndecoratedEdge hD e]
    apply (reverseUndecoratedEdge_isCorner_iff hD
      (unreversedUndecoratedEdge hD e)).mp
    exact D.strict_corner _ (Finset.mem_filter.mp he).2

/-- The reversed diagram is forward. -/
theorem reversedDiagram_forward (hD : Forward D) : Forward (reversedDiagram hD) := by
  intro e
  exact reversedUndecorated_forward hD e

theorem reversedDiagram_naturalEdge_iff (hD : Forward D) (u v : Fin n) :
    (∃ e : Edge (reversedDiagram hD).area, e.tail = u ∧ e.head = v) ↔
      ∃ f : Edge D.area, f.tail = v.rev ∧ f.head = u.rev :=
  reversedUndecorated_naturalEdge_iff hD u v

/-- Natural edges of a forward diagram correspond to natural edges of its reversal. -/
def reverseEdgeEquiv (hD : Forward D) :
    Edge D.area ≃ Edge (reversedDiagram hD).area where
  toFun := reverseUndecoratedEdge hD
  invFun := unreversedUndecoratedEdge hD
  left_inv := unreversed_reverseUndecoratedEdge hD
  right_inv := reverse_unreversedUndecoratedEdge hD

theorem reverseEdgeEquiv_tail (hD : Forward D) (e : Edge D.area) :
    (reverseEdgeEquiv hD e).tail = e.head.rev :=
  reverseUndecoratedEdge_tail hD e

theorem reverseEdgeEquiv_head (hD : Forward D) (e : Edge D.area) :
    (reverseEdgeEquiv hD e).head = e.tail.rev :=
  reverseUndecoratedEdge_head hD e

theorem reverseEdgeEquiv_strict_iff (hD : Forward D) (e : Edge D.area) :
    reverseEdgeEquiv hD e ∈ (reversedDiagram hD).strict ↔ e ∈ D.strict := by
  change reverseUndecoratedEdge hD e ∈
    Finset.univ.filter (fun f => unreversedUndecoratedEdge hD f ∈ D.strict) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    unreversed_reverseUndecoratedEdge]

theorem reverseEdgeEquiv_isCorner_iff (hD : Forward D) (e : Edge D.area) :
    IsCorner (reverseEdgeEquiv hD e) ↔ IsCorner e :=
  (reverseUndecoratedEdge_isCorner_iff hD e).symm

end

end VerticalStripLLT.Circular.DiagramProof

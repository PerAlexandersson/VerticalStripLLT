import VerticalStripLLT.Components.DiagramProof.NaturalRelations
import VerticalStripLLT.Components.IntervalDiagram

/-!
# Ordinary diagrams from their natural and strict relations

A forward interval-closed natural relation, together with strict pairs which are
maximal natural intervals, is realized by an actual ordinary diagram. Every
operation of the diagram proof changes these two relations and nothing else:
deleting a maximal corner, marking or unmarking corners, reordering blocks and
the NN/DN targets.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ}

/-- A natural relation is ordinary when it is forward and interval-closed. -/
structure OrdinaryRelation (N : Fin n → Fin n → Prop) : Prop where
  forward : ∀ u v, N u v → u < v
  interval : ∀ u v w, N u w → u < v → v < w → N u v ∧ N v w

/-- `s t` is a maximal pair of `N`. -/
def MaximalPair (N : Fin n → Fin n → Prop) (s t : Fin n) : Prop :=
  N s t ∧ ∀ x y, N x y → x ≤ s → t ≤ y → x = s ∧ y = t

theorem ordinaryRelation_naturalRel {D : Diagram n} (hD : Forward D) :
    OrdinaryRelation (naturalRel D) :=
  ⟨fun _ _ h => naturalRel_forward hD h,
    fun _ _ _ h huv hvw => naturalRel_interval hD h huv hvw⟩

theorem maximalPair_of_strictRel {D : Diagram n} (hD : Forward D) {s t : Fin n}
    (h : strictRel D s t) : MaximalPair (naturalRel D) s t :=
  ⟨naturalRel_of_strictRel h, fun _ _ hxy hxs hty => strictRel_maximal hD h hxy hxs hty⟩

/-- The undecorated diagram of an ordinary relation. -/
def ofNaturalRelation (N : Fin n → Fin n → Prop) (hN : OrdinaryRelation N) (hn : 0 < n) :
    Diagram n :=
  Diagram.ofIntervalRelation N (fun h huv hvw => hN.interval _ _ _ h huv hvw) hn

theorem ofNaturalRelation_naturalRel (N : Fin n → Fin n → Prop) (hN : OrdinaryRelation N)
    (hn : 0 < n) (u v : Fin n) : naturalRel (ofNaturalRelation N hN hn) u v ↔ N u v :=
  Diagram.ofIntervalRelation_naturalEdge_iff _ (fun h => hN.forward _ _ h) _ _ u v

theorem ofNaturalRelation_forward (N : Fin n → Fin n → Prop) (hN : OrdinaryRelation N)
    (hn : 0 < n) : Forward (ofNaturalRelation N hN hn) := fun e =>
  hN.forward _ _ ((ofNaturalRelation_naturalRel N hN hn _ _).mp ⟨e, rfl, rfl⟩)

/-- An ordinary diagram with prescribed natural and strict relations. -/
def ofRelations (N S : Fin n → Fin n → Prop) (hN : OrdinaryRelation N)
    (hS : ∀ s t, S s t → MaximalPair N s t) (hn : 0 < n) : Diagram n where
  area := (ofNaturalRelation N hN hn).area
  strict := Finset.univ.filter fun e => S e.tail e.head
  strict_corner := by
    intro e he
    have hU := ofNaturalRelation_forward N hN hn
    apply (isCorner_iff_maximal hU e).mpr
    intro g hgt hgh
    have hmax := (hS _ _ (Finset.mem_filter.mp he).2).2 g.tail g.head
      ((ofNaturalRelation_naturalRel N hN hn _ _).mp ⟨g, rfl, rfl⟩) hgt hgh
    exact (ofNaturalRelation N hN hn).endpointEmbedding.injective (Prod.ext hmax.1 hmax.2)

variable (N S : Fin n → Fin n → Prop) (hN : OrdinaryRelation N)
  (hS : ∀ s t, S s t → MaximalPair N s t) (hn : 0 < n)

theorem ofRelations_naturalRel (u v : Fin n) :
    naturalRel (ofRelations N S hN hS hn) u v ↔ N u v :=
  ofNaturalRelation_naturalRel N hN hn u v

theorem ofRelations_strictRel (u v : Fin n) :
    strictRel (ofRelations N S hN hS hn) u v ↔ S u v := by
  constructor
  · rintro ⟨e, he, rfl, rfl⟩
    exact (Finset.mem_filter.mp he).2
  · intro huv
    obtain ⟨e, rfl, rfl⟩ := (ofRelations_naturalRel N S hN hS hn u v).mpr (hS u v huv).1
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩, rfl, rfl⟩

theorem ofRelations_forward : Forward (ofRelations N S hN hS hn) :=
  ofNaturalRelation_forward N hN hn

/-! ### Removing maximal pairs -/

/-- Removing maximal pairs keeps a natural relation ordinary. -/
theorem OrdinaryRelation.removeMaximal {N : Fin n → Fin n → Prop} (hN : OrdinaryRelation N)
    (T : Fin n → Fin n → Prop) (hT : ∀ s t, T s t → MaximalPair N s t) :
    OrdinaryRelation (fun u v => N u v ∧ ¬ T u v) := by
  refine ⟨fun u v h => hN.forward u v h.1, ?_⟩
  rintro u v w ⟨huw, -⟩ huv hvw
  obtain ⟨huv', hvw'⟩ := hN.interval u v w huw huv hvw
  refine ⟨⟨huv', fun hT' => ?_⟩, ⟨hvw', fun hT' => ?_⟩⟩
  · exact hvw.ne ((hT u v hT').2 u w huw le_rfl hvw.le).2.symm
  · exact huv.ne ((hT v w hT').2 u w huw huv.le le_rfl).1

/-- A maximal pair stays maximal after removing pairs. -/
theorem MaximalPair.of_le {N N' : Fin n → Fin n → Prop} {s t : Fin n}
    (h : MaximalPair N s t) (hN' : ∀ u v, N' u v → N u v) (hst : N' s t) :
    MaximalPair N' s t :=
  ⟨hst, fun x y hxy => h.2 x y (hN' x y hxy)⟩

end

end VerticalStripLLT.Circular.DiagramProof

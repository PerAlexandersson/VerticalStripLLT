import VerticalStripLLT.Bridge.PathRelations
import VerticalStripLLT.Coloring
import VerticalStripLLT.OrientationExpansion
import VerticalStripLLT.Components.DiagramProof.Relational.RelationalDiagram
import VerticalStripLLT.Components.ForwardHRVBasic
import VerticalStripLLT.Circular.PairColoringBridge

/-!
# An ordinary Schröder path as a forward circular diagram

A path of positive size gives the forward diagram whose natural and strict relations
are those of the path (`toDiagram`, built with `ofRelations`). Its edges correspond
to the natural pairs of the path, its normal edges to the normal edges of the path,
and its states to the orientations of the path, with the same selected relation.
Hence the coloring sum and the shifted HRV expansion of the path are those of the
diagram.
-/

namespace VerticalStripLLT.SchroderPath

open Circular Circular.DiagramProof
open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} (P : SchroderPath n) (hn : 0 < n)

theorem naturalPair_ordinary : OrdinaryRelation P.NaturalPair :=
  ⟨fun _ _ h => P.naturalPair_forward h, fun _ _ _ h huv hvw => P.naturalPair_interval h huv hvw⟩

/-- The forward circular diagram with the natural and strict relations of `P`. -/
def toDiagram : Diagram n :=
  ofRelations P.NaturalPair (fun s t => (s, t) ∈ P.strictEdges) P.naturalPair_ordinary
    (fun _ _ h => P.strict_maximal h) hn

theorem toDiagram_forward : Forward (P.toDiagram hn) := ofRelations_forward _ _ _ _ hn

theorem mem_toDiagram_strict (e : Edge (P.toDiagram hn).area) :
    e ∈ (P.toDiagram hn).strict ↔ (e.tail, e.head) ∈ P.strictEdges := by
  exact (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ e).trans
    (and_iff_right (Finset.mem_univ _))

theorem naturalPair_of_edge (e : Edge (P.toDiagram hn).area) : P.NaturalPair e.tail e.head :=
  (ofRelations_naturalRel _ _ _ _ hn _ _).mp ⟨e, rfl, rfl⟩

theorem exists_edge_of_naturalPair {u v : Fin n} (h : P.NaturalPair u v) :
    ∃ e : Edge (P.toDiagram hn).area, e.tail = u ∧ e.head = v :=
  (ofRelations_naturalRel _ _ _ _ hn u v).mpr h

theorem edge_ext {e f : Edge (P.toDiagram hn).area} (ht : e.tail = f.tail)
    (hh : e.head = f.head) : e = f :=
  (P.toDiagram hn).endpointEmbedding.injective (Prod.ext ht hh)

/-- Normal edges of the diagram are the normal edges of the path. -/
theorem mem_toDiagram_normal (e : Edge (P.toDiagram hn).area) :
    e ∈ (P.toDiagram hn).edgeData.normalEdges ↔ (e.tail, e.head) ∈ P.normalEdges := by
  have hdis := Finset.disjoint_left.mp P.normalEdges_disjoint_strictEdges
  change e ∈ Finset.univ \ (P.toDiagram hn).strict ↔ _
  rw [Finset.mem_sdiff, mem_toDiagram_strict]
  rcases P.naturalPair_of_edge hn e with h | h
  · exact ⟨fun _ => h, fun h' => ⟨Finset.mem_univ _, hdis h'⟩⟩
  · exact ⟨fun h' => absurd h h'.2, fun h' => absurd h (hdis h')⟩

/-! ### Colorings -/

theorem toDiagram_pairGraph :
    (P.toDiagram hn).pairGraph = ⟨P.normalEdges, P.strictEdges⟩ := by
  have hnormal : (P.toDiagram hn).pairGraph.normalEdges = P.normalEdges := by
    ext x
    rw [Diagram.mem_pairGraph_normal_iff]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (P.mem_toDiagram_normal hn e).mp he
    · intro hx
      obtain ⟨e, ht, hh⟩ := P.exists_edge_of_naturalPair hn (u := x.1) (v := x.2) (Or.inl hx)
      refine ⟨e, (P.mem_toDiagram_normal hn e).mpr ?_, by rw [ht, hh]⟩
      rwa [ht, hh]
  have hstrict : (P.toDiagram hn).pairGraph.strictEdges = P.strictEdges := by
    ext x
    rw [Diagram.mem_pairGraph_strict_iff]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (P.mem_toDiagram_strict hn e).mp he
    · intro hx
      obtain ⟨e, ht, hh⟩ := P.exists_edge_of_naturalPair hn (u := x.1) (v := x.2) (Or.inr hx)
      refine ⟨e, (P.mem_toDiagram_strict hn e).mpr ?_, by rw [ht, hh]⟩
      rwa [ht, hh]
  cases h : (P.toDiagram hn).pairGraph
  rw [h] at hnormal hstrict
  subst hnormal hstrict
  rfl

/-- The coloring sum of the path is that of its diagram. -/
theorem toDiagram_coloringLLT (m : ℕ) : (P.toDiagram hn).coloringLLT m = coloringLLT P m := by
  rw [← Diagram.pairGraph_coloringLLT, toDiagram_pairGraph]
  rfl

/-! ### States -/

/-- The selected normal edges of the diagram given by an orientation of the path. -/
def toOrientation (θ : VerticalStripLLT.Orientation P) : Circular.Orientation (P.toDiagram hn) :=
  (P.toDiagram hn).orientationOfForward (P.toDiagram_forward hn)
    ((P.toDiagram hn).edgeData.normalEdges.filter fun e =>
      ∃ h : (e.tail, e.head) ∈ P.normalEdges, θ ⟨_, h⟩ = true)
    (Finset.filter_subset _ _)

theorem mem_toOrientation (θ : VerticalStripLLT.Orientation P)
    (e : Edge (P.toDiagram hn).area) :
    e ∈ (P.toOrientation hn θ).val ↔
      ∃ h : (e.tail, e.head) ∈ P.normalEdges, θ ⟨_, h⟩ = true := by
  simp only [toOrientation, Diagram.orientationOfForward, Finset.mem_filter]
  rw [mem_toDiagram_normal]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

/-- The selected relation of the diagram state is the upward step of the path. -/
theorem selected_toOrientation (θ : VerticalStripLLT.Orientation P) (u v : Fin n) :
    (P.toDiagram hn).edgeData.selected (P.toOrientation hn θ).val u v ↔ upwardStep P θ u v := by
  constructor
  · rintro ⟨e, he, rfl, rfl⟩
    rcases Finset.mem_union.mp he with hs | hA
    · exact Or.inl ((P.mem_toDiagram_strict hn e).mp hs)
    · exact Or.inr ((P.mem_toOrientation hn θ e).mp hA)
  · rintro (hs | ⟨hN, hθ⟩)
    · obtain ⟨e, rfl, rfl⟩ := P.exists_edge_of_naturalPair hn (Or.inr hs)
      exact ⟨e, Finset.mem_union_left _ ((P.mem_toDiagram_strict hn e).mpr hs), rfl, rfl⟩
    · obtain ⟨e, rfl, rfl⟩ := P.exists_edge_of_naturalPair hn (Or.inl hN)
      exact ⟨e, Finset.mem_union_right _ ((P.mem_toOrientation hn θ e).mpr ⟨hN, hθ⟩),
        rfl, rfl⟩

/-- The circular HRV of the diagram state is the ordinary HRV of the path orientation. -/
theorem hrv_toOrientation (θ : VerticalStripLLT.Orientation P) (u : Fin n) :
    (P.toOrientation hn θ).hrv u = hrv θ u := by
  have hrel : (P.toDiagram hn).edgeData.selected (P.toOrientation hn θ).val = upwardStep P θ := by
    funext u v
    exact propext (P.selected_toOrientation hn θ u v)
  have hf := P.toDiagram_forward hn
  apply le_antisymm
  · have h := (P.toOrientation hn θ).hrv_reachable u
    rw [hrel] at h
    exact reachable_le_hrv θ u _ h
  · apply (P.toOrientation hn θ).reachable_le_hrv_of_forward hf
    rw [hrel]
    exact reachable_hrv θ u

theorem hrvMonomial_toOrientation (θ : VerticalStripLLT.Orientation P) :
    (P.toOrientation hn θ).hrvMonomial = hrvMonomial θ := by
  unfold Circular.Orientation.hrvMonomial VerticalStripLLT.hrvMonomial
  apply Finset.prod_congr rfl
  intro r _
  have hfib : (Finset.univ.filter fun u => (P.toOrientation hn θ).hrv u = r) = hrvFiber θ r := by
    ext u
    simp [hrvFiber, P.hrv_toOrientation hn θ u]
  simp only [hfib]
  by_cases h : (hrvFiber θ r).Nonempty
  · rw [dite_eq_left (Finset.card_pos.mpr h), dite_eq_left h]
  · rw [dite_eq_right (by rwa [Finset.card_pos]), dite_eq_right h]

theorem card_toOrientation (θ : VerticalStripLLT.Orientation P) :
    (P.toOrientation hn θ).val.card = orientationAsc P θ := by
  unfold orientationAsc
  refine Finset.card_bij
    (fun e he => ⟨(e.tail, e.head), ((P.mem_toOrientation hn θ e).mp he).1⟩) ?_ ?_ ?_
  · intro e he
    obtain ⟨_, hθ⟩ := (P.mem_toOrientation hn θ e).mp he
    simpa using hθ
  · intro e _ f _ hef
    have h := congrArg Subtype.val hef
    exact P.edge_ext hn (Prod.mk.inj h).1 (Prod.mk.inj h).2
  · rintro ⟨⟨u, v⟩, hN⟩ hp
    obtain ⟨e, rfl, rfl⟩ := P.exists_edge_of_naturalPair hn (Or.inl hN)
    exact ⟨e, (P.mem_toOrientation hn θ e).mpr ⟨hN, by simpa using hp⟩, rfl⟩

theorem toOrientation_bijective : Function.Bijective (P.toOrientation hn) := by
  constructor
  · intro θ η h
    funext p
    obtain ⟨⟨u, v⟩, hN⟩ := p
    obtain ⟨e, rfl, rfl⟩ := P.exists_edge_of_naturalPair hn (Or.inl hN)
    have he := P.mem_toOrientation hn θ e
    rw [h, P.mem_toOrientation hn η e] at he
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hθ
      obtain ⟨_, hη⟩ := he.mpr ⟨hN, hθ⟩
      exact hη
    · intro hη
      obtain ⟨_, hθ⟩ := he.mp ⟨hN, hη⟩
      exact hθ
  · intro α
    refine ⟨fun p => decide (∃ e ∈ α.val, e.tail = p.1.1 ∧ e.head = p.1.2), ?_⟩
    apply Subtype.ext
    ext e
    rw [P.mem_toOrientation hn]
    constructor
    · rintro ⟨_, hd⟩
      obtain ⟨f, hf, ht, hh⟩ := of_decide_eq_true hd
      rwa [P.edge_ext hn ht hh] at hf
    · intro he
      have hN : e ∈ (P.toDiagram hn).edgeData.normalEdges := α.property.1 he
      exact ⟨(P.mem_toDiagram_normal hn e).mp hN, decide_eq_true ⟨e, he, rfl, rfl⟩⟩

/-- The shifted HRV expansion of the path is that of its diagram. -/
theorem toDiagram_shiftedOrientationExpansion :
    Circular.shiftedOrientationExpansion (P.toDiagram hn) =
      VerticalStripLLT.shiftedOrientationExpansion P := by
  unfold Circular.shiftedOrientationExpansion VerticalStripLLT.shiftedOrientationExpansion
    orientationExpansionAt
  symm
  apply Fintype.sum_bijective (P.toOrientation hn) (P.toOrientation_bijective hn)
  intro θ
  rw [P.card_toOrientation hn, P.hrvMonomial_toOrientation hn]

end

end VerticalStripLLT.SchroderPath

namespace VerticalStripLLT

/-- A path of size zero has coloring sum one. -/
theorem coloringLLT_size_zero (P : SchroderPath 0) (m : ℕ) : coloringLLT P m = 1 := by
  have hs : P.strictEdges = ∅ := Finset.eq_empty_of_forall_notMem fun e => Fin.elim0 e.1
  have hN : P.normalEdges = ∅ := Finset.eq_empty_of_forall_notMem fun e => Fin.elim0 e.1
  simp [coloringLLT, coloringWeight, admissible, ascentCount, hs, hN]

/-- A path of size zero has shifted HRV expansion one. -/
theorem shiftedOrientationExpansion_size_zero (P : SchroderPath 0) :
    shiftedOrientationExpansion P = 1 := by
  classical
  let : IsEmpty {e // e ∈ P.normalEdges} := ⟨fun e => Fin.elim0 e.1.1⟩
  have ha (θ : Orientation P) : orientationAsc P θ = 0 := by
    simp [orientationAsc, Finset.univ_eq_empty]
  simp [shiftedOrientationExpansion, orientationExpansionAt, ha, hrvMonomial]

end VerticalStripLLT

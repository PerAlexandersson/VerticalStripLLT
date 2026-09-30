import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! A one-edge exchange between connected finite simple graphs. -/

namespace VerticalStripLLT.Circular.DiagramProof

namespace SimpleGraph

open _root_.SimpleGraph

variable {V : Type*}

private theorem reachable_deleteEdges_or_other_endpoint (H : SimpleGraph V) (a b v : V)
    (hH : H.Connected) :
    (H.deleteEdges {s(a, b)}).Reachable a v ∨
      (H.deleteEdges {s(a, b)}).Reachable b v := by
  classical
  rcases hH.preconnected a v with ⟨p⟩
  let q : H.Path a v := p.toPath
  by_cases heq : s(a, b) ∈ (q : H.Walk a v).edges
  · right
    rcases q with ⟨q, hq⟩
    cases q with
    | nil => simp at heq
    | @cons u w z hadj q =>
      have hbw : b = w := by
        simpa using hq.eq_snd_of_mem_edges heq
      have htail : s(a, b) ∉ q.edges := by
        have htrail := (_root_.SimpleGraph.Walk.isTrail_cons hadj q).mp hq.isTrail
        simpa [hbw] using htrail.2
      refine ⟨(q.toDeleteEdges {s(a, b)} ?_).copy hbw.symm rfl⟩
      intro e he
      rw [Set.mem_singleton_iff]
      intro h
      exact htail (h ▸ he)
  · left
    refine ⟨(q : H.Walk a v).toDeleteEdges {s(a, b)} ?_⟩
    intro e he
    rw [Set.mem_singleton_iff]
    intro h
    exact heq (h ▸ he)

private theorem exists_adj_across_reachable (G J : SimpleGraph V) (a : V)
    {u v : V} (p : J.Walk u v) (hu : G.Reachable a u) (hv : ¬ G.Reachable a v) :
    ∃ x y, J.Adj x y ∧ G.Reachable a x ∧ ¬ G.Reachable a y := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u v w huv p ih =>
    by_cases hav : G.Reachable a v
    · exact ih hav hv
    · exact ⟨u, v, huv, hu, hav⟩

private theorem connected_of_replacing_edge (H K : SimpleGraph V) (e : Sym2 V)
    (hH : H.Connected)
    (hkeep : ∀ ⦃u v : V⦄, H.Adj u v → s(u, v) ≠ e → K.Adj u v)
    (hreplacement : ∀ ⦃u v : V⦄, s(u, v) = e → K.Reachable u v) : K.Connected := by
  refine { preconnected := ?_, nonempty := hH.nonempty }
  intro u v
  rcases hH.preconnected u v with ⟨p⟩
  induction p with
  | nil => exact .rfl
  | @cons u v w huv p ih =>
      by_cases heq : s(u, v) = e
      · exact (hreplacement heq).trans ih
      · exact (hkeep huv heq).reachable.trans ih

/-- A target connected graph supplies an edge reconnecting a bridge deleted from `H`.
The receiver is outside `H`; no cardinality hypothesis is needed in the bridge case. -/
theorem exists_reconnecting_edge (H J : SimpleGraph V) (a b : V)
    (hH : H.Connected) (hJ : J.Connected) (hbridge : H.IsBridge s(a, b))
    (hnotJ : s(a, b) ∉ J.edgeSet) :
    ∃ f ∈ J.edgeSet \ H.edgeSet,
      (H.deleteEdges {s(a, b)} ⊔ SimpleGraph.fromEdgeSet {f}).Connected := by
  classical
  let G := H.deleteEdges {s(a, b)}
  have hab : ¬ G.Reachable a b := by
    simpa [G] using (_root_.SimpleGraph.isBridge_iff.mp hbridge)
  rcases hJ.preconnected a b with ⟨p⟩
  rcases exists_adj_across_reachable G J a p .rfl hab with ⟨x, y, hxy, hax, hay⟩
  let f := s(x, y)
  have hfJ : f ∈ J.edgeSet := J.mem_edgeSet.mpr hxy
  have hfH : f ∉ H.edgeSet := by
    intro hfH
    have hHxy : H.Adj x y := H.mem_edgeSet.mp hfH
    by_cases hfe : f = s(a, b)
    · exact hnotJ (hfe ▸ hfJ)
    · exact hay (hax.trans (by
        exact (_root_.SimpleGraph.deleteEdges_adj.mpr ⟨hHxy, hfe⟩ : G.Adj x y).reachable))
  have hby : G.Reachable b y := by
    rcases reachable_deleteEdges_or_other_endpoint H a b y hH with hay' | hby
    · exact (hay hay').elim
    · exact hby
  have hKab : (G ⊔ SimpleGraph.fromEdgeSet {f}).Reachable a b := by
    have hxyK : (G ⊔ SimpleGraph.fromEdgeSet {f}).Reachable x y := by
      apply _root_.SimpleGraph.Adj.reachable
      exact Or.inr ⟨by simp [f], hxy.ne⟩
    exact (hax.mono le_sup_left).trans (hxyK.trans (hby.mono le_sup_left).symm)
  refine ⟨f, ⟨hfJ, hfH⟩, ?_⟩
  apply connected_of_replacing_edge H (G ⊔ SimpleGraph.fromEdgeSet {f}) s(a, b) hH
  · intro u v huv huvne
    apply Or.inl
    exact (_root_.SimpleGraph.deleteEdges_adj.mpr ⟨huv, huvne⟩ : G.Adj u v)
  · intro u v huv
    rcases Sym2.eq_iff.mp huv with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hKab
    · rcases h with ⟨rfl, rfl⟩
      exact hKab.symm

/-- Exchange a donor edge of one connected finite graph for a receiver edge of another.
The equal-cardinality hypothesis is only used when deleting the donor leaves `H` connected. -/
theorem exists_connected_edge_exchange [Fintype V] (H J : SimpleGraph V) (a b : V)
    (hH : H.Connected) (hJ : J.Connected) (heH : s(a, b) ∈ H.edgeSet)
    (heJ : s(a, b) ∉ J.edgeSet) (hcard : Nat.card H.edgeSet = Nat.card J.edgeSet) :
    ∃ f ∈ J.edgeSet \ H.edgeSet,
      (H.deleteEdges {s(a, b)} ⊔ SimpleGraph.fromEdgeSet {f}).Connected := by
  classical
  by_cases hbridge : H.IsBridge s(a, b)
  · exact exists_reconnecting_edge H J a b hH hJ hbridge heJ
  · have hdelete : (H.deleteEdges {s(a, b)}).Connected :=
      hH.preconnected.connected_deleteEdges_of_not_isBridge hbridge
    have hreceiver : ∃ f ∈ J.edgeSet, f ∉ H.edgeSet := by
      by_contra! hno
      have hsub : J.edgeSet ⊆ H.edgeSet := fun f hf => hno f hf
      have hsub' : J.edgeFinset ⊆ H.edgeFinset :=
        _root_.SimpleGraph.edgeFinset_mono
          (_root_.SimpleGraph.edgeSet_subset_edgeSet.mp hsub)
      have hstrict : J.edgeFinset ⊂ H.edgeFinset := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub', ?_⟩
        intro hEq
        have : s(a, b) ∈ J.edgeFinset := by
          rw [hEq]
          exact SimpleGraph.mem_edgeFinset.mpr heH
        exact heJ (SimpleGraph.mem_edgeFinset.mp this)
      have hlt := Finset.card_lt_card hstrict
      rw [_root_.SimpleGraph.edgeFinset_card, _root_.SimpleGraph.edgeFinset_card] at hlt
      simp only [Nat.card_eq_fintype_card] at hcard
      lia
    rcases hreceiver with ⟨f, hfJ, hfH⟩
    refine ⟨f, ⟨hfJ, hfH⟩, hdelete.mono le_sup_left⟩

end SimpleGraph

end VerticalStripLLT.Circular.DiagramProof

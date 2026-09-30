import VerticalStripLLT.Components.DiagramProof.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Finite simple graphs represented by selected diagram-edge sets. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The simple graph obtained by forgetting the directions of a finite edge set. -/
def edgeSetGraph (A : Finset (Edge D.area)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => ∃ e ∈ A, e.tail = u ∧ e.head = v)

/-- Sending a forward edge to its unordered pair of endpoints is injective. -/
def edgeSym2Embedding (hforward : Forward D) : Edge D.area ↪ Sym2 (Fin n) where
  toFun e := s(e.tail, e.head)
  inj' e f h := by
    rcases Sym2.eq_iff.mp h with h | h
    · exact D.endpointEmbedding.injective (Prod.ext h.1 h.2)
    · exfalso
      have hef : f.head < f.tail := by simpa only [h.1, h.2] using hforward e
      exact (not_lt_of_ge (hforward f).le) hef

theorem edgeSetGraph_mono {A B : Finset (Edge D.area)} (hAB : A ⊆ B) :
    edgeSetGraph A ≤ edgeSetGraph B := by
  intro u v huv
  rcases huv with ⟨huv, h | h⟩
  · exact ⟨huv, Or.inl (by
      rcases h with ⟨e, he, ht, hh⟩
      exact ⟨e, hAB he, ht, hh⟩)⟩
  · exact ⟨huv, Or.inr (by
      rcases h with ⟨e, he, ht, hh⟩
      exact ⟨e, hAB he, ht, hh⟩)⟩

/-- On forward diagram edges, adjacency in the finite graph has the given orientation exactly
when the edge is present. -/
theorem edgeSetGraph_adj_iff_mem (hforward : Forward D) (A : Finset (Edge D.area))
    (e : Edge D.area) : (edgeSetGraph A).Adj e.tail e.head ↔ e ∈ A := by
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with ⟨f, hf, ht, hh⟩
      have hef : f = e := D.endpointEmbedding.injective (Prod.ext ht hh)
      exact hef ▸ hf
    · rcases h with ⟨f, hf, ht, hh⟩
      have hfe : e.head < e.tail := by simpa only [ht, hh] using hforward f
      exact (not_lt_of_ge (hforward e).le hfe).elim
  · intro he
    exact ⟨(hforward e).ne, Or.inl ⟨e, he, rfl, rfl⟩⟩

theorem edgeSetGraph_edgeFinset (hforward : Forward D) (A : Finset (Edge D.area)) :
    (edgeSetGraph A).edgeFinset = A.map (edgeSym2Embedding hforward) := by
  ext x
  refine Sym2.inductionOn x ?_
  intro u v
  rw [SimpleGraph.mem_edgeFinset]
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with ⟨e, he, ht, hh⟩
      refine ⟨e, he, ?_⟩
      change s(e.tail, e.head) = s(u, v)
      rw [ht, hh]
    · rcases h with ⟨e, he, ht, hh⟩
      refine ⟨e, he, ?_⟩
      change s(e.tail, e.head) = s(u, v)
      rw [ht, hh, Sym2.eq_swap]
  · rintro ⟨e, he, h⟩
    have heq := Sym2.eq_iff.mp h
    rcases heq with heq | heq
    · refine ⟨?_, Or.inl ⟨e, he, heq.1, heq.2⟩⟩
      simpa only [heq.1, heq.2] using (hforward e).ne
    · refine ⟨?_, Or.inr ⟨e, he, heq.1, heq.2⟩⟩
      simpa only [heq.1, heq.2] using (hforward e).ne.symm

theorem edgeSetGraph_card (hforward : Forward D) (A : Finset (Edge D.area)) :
    Nat.card (edgeSetGraph A).edgeSet = A.card := by
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    edgeSetGraph_edgeFinset hforward, Finset.card_map]

/-- Erasing one forward diagram edge is exactly deletion of its undirected edge. -/
theorem edgeSetGraph_erase (hforward : Forward D) (A : Finset (Edge D.area))
    (d : Edge D.area) :
    edgeSetGraph (A.erase d) = (edgeSetGraph A).deleteEdges {s(d.tail, d.head)} := by
  apply SimpleGraph.edgeSet_injective
  ext x
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
  rw [← SimpleGraph.mem_edgeFinset, ← SimpleGraph.mem_edgeFinset]
  rw [edgeSetGraph_edgeFinset hforward, edgeSetGraph_edgeFinset hforward,
    Finset.map_erase, Finset.mem_erase]
  exact and_comm

/-- The edges of `A` retained by a subgraph of `edgeSetGraph A`. -/
def edgeSetGraphSub (A : Finset (Edge D.area)) (H : SimpleGraph (Fin n)) :
    Finset (Edge D.area) :=
  A.filter fun e => H.Adj e.tail e.head

theorem edgeSetGraphSub_subset (A : Finset (Edge D.area)) (H : SimpleGraph (Fin n)) :
    edgeSetGraphSub A H ⊆ A := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem edgeSetGraphSub_eq_of_le (A : Finset (Edge D.area)) (H : SimpleGraph (Fin n))
    (hH : H ≤ edgeSetGraph A) : edgeSetGraph (edgeSetGraphSub A H) = H := by
  ext u v
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with ⟨e, he, ht, hh⟩
      have hsel := (Finset.mem_filter.mp he).2
      simpa only [ht, hh] using hsel
    · rcases h with ⟨e, he, ht, hh⟩
      have hsel := (Finset.mem_filter.mp he).2
      simpa only [ht, hh] using hsel.symm
  · intro huv
    rcases hH huv with ⟨hne, h | h⟩
    · rcases h with ⟨e, he, ht, hh⟩
      refine ⟨hne, Or.inl ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, ht, hh⟩⟩
      simpa only [ht, hh] using huv
    · rcases h with ⟨e, he, ht, hh⟩
      refine ⟨hne, Or.inr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, ht, hh⟩⟩
      simpa only [ht, hh] using huv.symm

end

end VerticalStripLLT.Circular.DiagramProof

import VerticalStripLLT.Components.DiagramProof.LastCliqueFixedEdges
import VerticalStripLLT.Components.DiagramProof.TreeLeaves

/-! The fixed selection is exactly the core tree with the omitted vertices attached as leaves. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

theorem lastCliqueFixedEdges_isTree (hD : Forward D)
    (ι : Fin (k + 1) ↪o Fin n) (c : Fin n) (g : Edge D.area) (hgc : g.tail ≤ c)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree)
    (hTG : T ≤ edgeSetGraph (Finset.univ : Finset (Edge (inducedDiagram hD ι).area))) :
    (edgeSetGraph (lastCliqueFixedEdges hD ι c g T)).IsTree := by
  obtain ⟨j, hj⟩ := (himage g.head).mpr (Or.inr rfl)
  let A := lastCliqueFixedEdges hD ι c g T
  let H := SimpleGraph.fromRel (fun x y : Fin n =>
    (∃ u v : Fin (k + 1), T.Adj u v ∧ ι u = x ∧ ι v = y) ∨
    (x ∉ Set.range ι ∧ y = ι j))
  have hAto (e : Edge D.area) (he : e ∈ A) : H.Adj e.tail e.head := by
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
      change H.Adj (inducedEdge hD ι f).tail (inducedEdge hD ι f).head
      rw [inducedEdge_tail, inducedEdge_head]
      exact ⟨(ι.strictMono (inducedDiagram_forward hD ι f)).ne,
        Or.inl (Or.inl ⟨f.tail, f.head, (Finset.mem_filter.mp hf).2, rfl, rfl⟩)⟩
    · obtain ⟨hc, hh⟩ := (Finset.mem_filter.mp he).2
      have hout : e.tail ∉ Set.range ι := by
        intro hi
        rcases (himage e.tail).mp hi with hi | hi
        · exact (not_le_of_gt hc) hi
        · have hlt := hD e
          rw [hi, hh] at hlt
          exact lt_irrefl _ hlt
      exact ⟨(hD e).ne, Or.inl (Or.inr ⟨hout, hh.trans hj.symm⟩)⟩
  have hcore {u v : Fin (k + 1)} (huv : T.Adj u v) :
      (edgeSetGraph A).Adj (ι u) (ι v) := by
    rcases hTG huv with ⟨_, h | h⟩
    · obtain ⟨e, _, ht, hh⟩ := h
      have heT : T.Adj e.tail e.head := by simpa only [ht, hh] using huv
      have hadj := (edgeSetGraph_adj_iff_mem hD A (inducedEdge hD ι e)).mpr
        (inducedEdge_mem_lastCliqueFixedEdges hD ι c g T e heT)
      simpa only [inducedEdge_tail, inducedEdge_head, ht, hh] using hadj
    · obtain ⟨e, _, ht, hh⟩ := h
      have heT : T.Adj e.tail e.head := by simpa only [ht, hh] using huv.symm
      have hadj := (edgeSetGraph_adj_iff_mem hD A (inducedEdge hD ι e)).mpr
        (inducedEdge_mem_lastCliqueFixedEdges hD ι c g T e heT)
      simpa only [inducedEdge_tail, inducedEdge_head, ht, hh] using hadj.symm
  have hleaf {x : Fin n} (hx : x ∉ Set.range ι) : (edgeSetGraph A).Adj x (ι j) := by
    have hcx : c < x := lt_of_not_ge (fun h => hx ((himage x).mpr (Or.inl h)))
    have hxe : x < g.head := lt_of_le_of_ne (hlast x) (fun h => hx ⟨j, hj.trans h.symm⟩)
    obtain ⟨e, ht, hh⟩ := exists_edge_of_naturalLift_of_le
      (D.naturalLift_of_tail_lt_head g (hD g)) (hgc.trans hcx.le) hxe le_rfl
    have heA : e ∈ A := Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [ht] using hcx, hh⟩)
    have hadj := (edgeSetGraph_adj_iff_mem hD A e).mpr heA
    simpa only [ht, hh, hj] using hadj
  have hEq : edgeSetGraph A = H := by
    ext x y
    constructor
    · rintro ⟨_, h | h⟩
      · obtain ⟨e, he, ht, hh⟩ := h
        simpa only [ht, hh] using hAto e he
      · obtain ⟨e, he, ht, hh⟩ := h
        simpa only [ht, hh] using (hAto e he).symm
    · rintro ⟨_, h | h⟩
      · rcases h with ⟨u, v, huv, rfl, rfl⟩ | ⟨hx, rfl⟩
        · exact hcore huv
        · exact hleaf hx
      · rcases h with ⟨u, v, huv, rfl, rfl⟩ | ⟨hy, rfl⟩
        · exact (hcore huv).symm
        · exact (hleaf hy).symm
  change (edgeSetGraph A).IsTree
  rw [hEq]
  exact tree_with_attached_leaves ι.toEmbedding j T hT

end

end VerticalStripLLT.Circular.DiagramProof

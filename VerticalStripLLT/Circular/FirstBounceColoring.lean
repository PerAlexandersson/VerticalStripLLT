import VerticalStripLLT.Circular.PairBounce
import VerticalStripLLT.Circular.ShortenStrictPairs

/-! The NN coloring identity for the actual shortened circular diagram. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

noncomputable def firstBounceBackground (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val) : PairGraph n where
  normalEdges := D.pairGraph.normalEdges.erase
    ((D.shortenedOldEdge e he hlen).tail, e.head)
  strictEdges := D.pairGraph.strictEdges.erase (e.tail, e.head)

/-- Only the exterior swap symmetries remain as hypotheses of this graph-level adapter. -/
theorem coloringLLT_shortenStrict_of_pair_symmetry (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hbridge : (e.tail, (D.shortenedOldEdge e he hlen).tail) ∈
      (D.firstBounceBackground e he hlen).normalEdges)
    (hs : (D.firstBounceBackground e he hlen).strictEdges.map
      (swapVertexPair e.tail (D.shortenedOldEdge e he hlen).tail) =
        (D.firstBounceBackground e he hlen).strictEdges)
    (hn : ((D.firstBounceBackground e he hlen).normalEdges.erase
      (e.tail, (D.shortenedOldEdge e he hlen).tail)).map
        (swapVertexPair e.tail (D.shortenedOldEdge e he hlen).tail) =
          (D.firstBounceBackground e he hlen).normalEdges.erase
            (e.tail, (D.shortenedOldEdge e he hlen).tail)) (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X *
      (D.shortenStrict e he hlen hgap).coloringLLT m := by
  classical
  let f := D.shortenedOldEdge e he hlen
  have hf : (f.tail, e.head) ∈ D.pairGraph.normalEdges := by
    apply (D.mem_pairGraph_normal_iff _).mpr
    refine ⟨f, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact D.shortened_old_edge_not_strict e he hlen
  have hepair : (e.tail, e.head) ∈ D.pairGraph.strictEdges :=
    (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩
  rw [← D.pairGraph_coloringLLT, ← (D.shortenStrict e he hlen hgap).pairGraph_coloringLLT]
  apply PairGraph.coloringLLT_eq_C_X_mul_of_edges
    (B := D.firstBounceBackground e he hlen) (i := e.tail) (y := f.tail) (z := e.head)
  · exact (Finset.insert_erase hf).symm
  · exact (Finset.insert_erase hepair).symm
  · exact D.shortenStrict_pairGraph_normalEdges e he hlen hgap
  · exact D.shortenStrict_pairGraph_strictEdges e he hlen hgap
  · exact Finset.notMem_erase _ _
  · exact hbridge
  · exact hs
  · exact hn
  · exact e.tail_ne_head.symm
  · exact f.tail_ne_head.symm

end Diagram
end VerticalStripLLT.Circular

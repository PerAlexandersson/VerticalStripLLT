import VerticalStripLLT.Circular.DNTargetPairs
import VerticalStripLLT.Circular.PairBounce

/-! Pair-graph coloring bridge for a direct-contact DN successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

noncomputable def secondBounceBackground (e f : Edge D.area) : PairGraph n where
  normalEdges := D.pairGraph.normalEdges.erase (D.area.next f.tail, f.head)
  strictEdges := (D.pairGraph.strictEdges.erase (e.tail, e.head)).erase (f.tail, f.head)

/-- The coloring identity for the actual DN successor, conditional only on the
remaining local normal-edge and exterior-symmetry geometry. -/
theorem coloringLLT_dnSuccessor_of_pair_data
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hfe : f ≠ e)
    (hcontact : f.tail = e.head)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)
    (hsource_normal : D.pairGraph.normalEdges =
      insert (D.area.next f.tail, f.head) (D.secondBounceBackground e f).normalEdges)
    (htarget_normal :
      (D.dnSuccessor e f he hf hfe heq hb hns hlen hgap).pairGraph.normalEdges =
        insert (e.tail, e.head) (D.secondBounceBackground e f).normalEdges)
    (hfresh_yz : (D.area.next f.tail, f.head) ∉ (D.secondBounceBackground e f).normalEdges)
    (hfresh_ai : (e.tail, e.head) ∉ (D.secondBounceBackground e f).normalEdges)
    (hiy : (e.head, D.area.next f.tail) ∈ (D.secondBounceBackground e f).normalEdges)
    (hstrict_swap : (D.secondBounceBackground e f).strictEdges.map
      (swapVertexPair e.head (D.area.next f.tail)) = (D.secondBounceBackground e f).strictEdges)
    (hnormal_swap : ((D.secondBounceBackground e f).normalEdges.erase
      (e.head, D.area.next f.tail)).map
        (swapVertexPair e.head (D.area.next f.tail)) =
      (D.secondBounceBackground e f).normalEdges.erase (e.head, D.area.next f.tail))
    (hai : e.tail ≠ e.head) (hay : e.tail ≠ D.area.next f.tail)
    (hzi : f.head ≠ e.head) (hzy : f.head ≠ D.area.next f.tail) (m : ℕ) :
    D.coloringLLT m = (D.dnSuccessor e f he hf hfe heq hb hns hlen hgap).coloringLLT m := by
  let Q := D.dnSuccessor e f he hf hfe heq hb hns hlen hgap
  have hsource_strict : D.pairGraph.strictEdges = insert (e.tail, e.head)
      (insert (e.head, f.head) (D.secondBounceBackground e f).strictEdges) := by
    have heP := (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩
    have hfP := (D.mem_pairGraph_strict_iff _).mpr ⟨f, hf, rfl⟩
    change _ = insert (e.tail, e.head) (insert (e.head, f.head)
      ((D.pairGraph.strictEdges.erase (e.tail, e.head)).erase (f.tail, f.head)))
    have hneP : (f.tail, f.head) ≠ (e.tail, e.head) :=
      fun h => hfe (D.endpointEmbedding.injective h)
    simp only [hcontact] at hfP hneP ⊢
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hneP, hfP⟩),
      Finset.insert_erase heP]
  have htarget_strict : Q.pairGraph.strictEdges = insert (e.tail, D.area.next e.head)
      (insert (D.area.next f.tail, f.head) (D.secondBounceBackground e f).strictEdges) := by
    simpa only [Q, secondBounceBackground, hcontact, Finset.insert_comm] using
      D.dnSuccessor_pairGraph_strictEdges e f he hf hfe heq hb hns hlen hgap
  rw [← D.pairGraph_coloringLLT, ← Q.pairGraph_coloringLLT]
  exact PairGraph.coloringLLT_eq_of_secondBounce_edges D.pairGraph Q.pairGraph
    (D.secondBounceBackground e f) e.tail e.head (D.area.next f.tail) f.head
    hsource_normal hsource_strict htarget_normal
    (by simpa only [hcontact] using htarget_strict) hfresh_yz hfresh_ai hiy
    hstrict_swap hnormal_swap hai hay hzi hzy

end Diagram
end VerticalStripLLT.Circular

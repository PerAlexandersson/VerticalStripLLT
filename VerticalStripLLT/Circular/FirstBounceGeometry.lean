import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.FirstBounceColoring
import VerticalStripLLT.Circular.FirstBounceStrictSwap
import VerticalStripLLT.Circular.NaturalPairSwap
import VerticalStripLLT.Circular.PairBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Geometric hypotheses for the first circular NN bounce. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem coloringLLT_firstBounce_geometry
    {e : Edge D.area} (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (hsame : D.boundary (D.boundary (e.head.val : ℤ) + 1) =
      D.boundary (D.boundary (e.head.val : ℤ)))
    (hleft : ¬ D.strictAt (D.boundary (e.head.val : ℤ)))
    (hright : ¬ D.strictAt (D.boundary (e.head.val : ℤ) + 1)) (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X *
      (D.shortenStrict e he hlen hgap).coloringLLT m := by
  classical
  let z : ℤ := e.head.val
  let p : ℤ := D.boundary z
  have hzhead : e.head = D.residue z := by
    dsimp [z]
    exact (Orientation.residue_intCast_eq (D := D) e.head).symm
  have hsame' : D.boundary (p + 1) = D.boundary p := by
    simpa [p, z] using hsame
  have hbound : p + 2 ≤ D.boundary (z + 1) := by
    change D.boundary z + 2 ≤ D.boundary (z + 1)
    simp only [Diagram.boundary, D.residue_succ, ← hzhead]
    have hgap' : (D.area.area (D.area.next e.head) : ℤ) <
        (D.area.area e.head : ℤ) := by exact_mod_cast hgap
    lia
  have hno : ∀ w k : ℤ, D.boundary w ≠ p + 1 + (n : ℤ) * k := by
    intro w k hw
    have hgap0 := D.no_boundary_gap z p rfl hbound
    apply hgap0 (w + (n : ℤ) * (-k))
    rw [D.boundary_add_period, hw]
    ring
  have hn : 2 ≤ n := by
    have hp := e.length_pos
    have hlt := e.length_lt_n
    lia
  have he_tail : e.tail = D.residue p := by
    simpa [p, z] using D.strictEdge_tail_boundary he
  let f := D.shortenedOldEdge e he hlen
  have hf_tail : f.tail = D.residue (p + 1) := by
    change (D.shortenedOldEdge e he hlen).tail = _
    rw [D.shortenedOldEdge_tail e he hlen, he_tail, D.residue_succ]
  have hstrict :
      (D.pairGraph.strictEdges.erase (e.tail, e.head)).map
          (swapVertexPair e.tail f.tail) =
        D.pairGraph.strictEdges.erase (e.tail, e.head) := by
    have hs := D.firstBounce_strict_exterior_swap he p he_tail hleft hright hno
    simpa only [he_tail, hf_tail] using hs
  have hnat :
      (D.naturalPairs.erase (e.tail, f.tail)).map
          (swapVertexPair e.tail f.tail) =
        D.naturalPairs.erase (e.tail, f.tail) := by
    simpa only [he_tail, hf_tail] using D.naturalPairs_erase_map_swap hn p hsame' hno
  have hpair : (e.tail, e.head) ∈ D.pairGraph.strictEdges := by
    exact (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩
  have hzi : e.head ≠ e.tail := e.tail_ne_head.symm
  have hzy : e.head ≠ f.tail := by
    intro h
    apply hright
    exact ⟨e, he, h.trans hf_tail⟩
  have hnormal :
      (((D.naturalPairs \ D.pairGraph.strictEdges).erase (f.tail, e.head)).erase
        (e.tail, f.tail)).map (swapVertexPair e.tail f.tail) =
        ((D.naturalPairs \ D.pairGraph.strictEdges).erase (f.tail, e.head)).erase
          (e.tail, f.tail) := by
    exact normal_background_swap D.naturalPairs D.pairGraph.strictEdges
      e.tail f.tail e.head hpair hzi hzy hnat hstrict
  have hbridge : (e.tail, f.tail) ∈
      (D.firstBounceBackground e he hlen).normalEdges := by
    have hlift : D.boundaryNaturalLift p (p + 1) := by
      constructor
      · rw [hsame']
        exact D.boundary_le_self p
      · lia
    let g := D.edgeFromLift p (p + 1) hlift
    have hgnot : g ∉ D.strict := by
      intro hg
      exact hright ((D.edgeFromLift_mem_strict_iff hlift).mp hg).1
    have hpairg : (g.tail, g.head) = (e.tail, f.tail) := by
      change ((D.edgeFromLift _ _ hlift).tail, (D.edgeFromLift _ _ hlift).head) = _
      rw [D.edgeFromLift_tail hlift, D.edgeFromLift_head hlift, he_tail, hf_tail]
    have hnormalg : (g.tail, g.head) ∈ D.pairGraph.normalEdges := by
      apply (D.mem_pairGraph_normal_iff _).mpr
      exact ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hgnot⟩, rfl⟩
    have hne : (e.tail, f.tail) ≠ (f.tail, e.head) := by
      intro heq
      have : e.tail = f.tail := congrArg Prod.fst heq
      exact (D.residue_p_ne_succ hn p) (he_tail.symm.trans (this.trans hf_tail))
    change (e.tail, f.tail) ∈ D.pairGraph.normalEdges.erase (f.tail, e.head)
    exact Finset.mem_erase.mpr ⟨hne, by simpa [hpairg] using hnormalg⟩
  apply D.coloringLLT_shortenStrict_of_pair_symmetry e he hlen hgap hbridge
    (m := m)
  · simpa only [firstBounceBackground, f] using hstrict
  · simpa only [firstBounceBackground, f, D.normalPairs_eq_sdiff] using hnormal

end Diagram
end VerticalStripLLT.Circular
